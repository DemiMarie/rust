// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use build::{BlockAnd, BlockAndExtension, Builder};
use build::scope::LoopScope;
use hair::*;
use rustc::mir::*;
use std::io::{stdout, Write};

impl<'a, 'gcx, 'tcx> Builder<'a, 'gcx, 'tcx> {
    fn build_become(&mut self, mut block: BasicBlock, value: ExprRef<'tcx>,
                    source_info: SourceInfo) -> BlockAnd<()> {
        let this = self;
        let expr = this.hir.mirror(value);

        // Find the actual call site
        let (_, fun, args) = match expr.kind {
            ExprKind::Call { ty, fun, args } => (ty, fun, args),
            ExprKind::Scope { extent, value } => {
                return this.in_scope(extent, block, |this|
                                     this.build_become(block, value, source_info))
            }
            // Impossible – would not typecheck
            _ => span_bug!(expr.span,
                           "Can only `become` a call expression \
                           (this should have been detected earlier): `{:?}`",
                           expr),
        };
        let mut args_ = vec![];

        // Move each argument to the function into a separate temp variable
        // for which no drop is scheduled.
        let fun = this.hir.mirror(fun);
        let fun = unpack!(block = this.as_operand(block, fun));

        for arg in args.into_iter() {
            let expr: Expr = this.hir.mirror(arg);
            let temp = this.temp(expr.ty.clone());
            let operand = unpack!(block = this.as_rvalue(block, expr));
            this.cfg.push_assign(block, source_info, &temp, operand);
            args_.push(Operand::Consume(temp))
        }
        // Drop everything in the current function EXCEPT the temp variables
        // created above
        let extent = this.extent_of_return_scope();
        let new_block = this.cfg.start_new_block();

        println!("Made it to exit_scope");
        let _ = stdout().flush();
        // Branches into `new_block`!
        this.exit_scope(expr.span, extent, block, new_block);

        println!("Made it to terminate");
        let _ = stdout().flush();
        this.cfg.terminate(new_block, source_info, TerminatorKind::TailCall {
            func: fun,
            args: args_,
        });
        println!("Made it to start_new_block");
        let _ = stdout().flush();
        this.cfg.start_new_block().unit()
    }

    pub fn stmt_expr(&mut self, mut block: BasicBlock, expr: Expr<'tcx>) -> BlockAnd<()> {
        let this = self;
        let expr_span = expr.span;
        let source_info = this.source_info(expr.span);
        // Handle a number of expressions that don't need a destination at all. This
        // avoids needing a mountain of temporary `()` variables.
        match expr.kind {
            ExprKind::Scope { extent, value } => {
                let value = this.hir.mirror(value);
                this.in_scope(extent, block, |this| this.stmt_expr(block, value))
            }
            ExprKind::Assign { lhs, rhs } => {
                let lhs = this.hir.mirror(lhs);
                let rhs = this.hir.mirror(rhs);
                let lhs_span = lhs.span;

                // Note: we evaluate assignments right-to-left. This
                // is better for borrowck interaction with overloaded
                // operators like x[j] = x[i].

                // Generate better code for things that don't need to be
                // dropped.
                if this.hir.needs_drop(lhs.ty) {
                    let rhs = unpack!(block = this.as_operand(block, rhs));
                    let lhs = unpack!(block = this.as_lvalue(block, lhs));
                    unpack!(block = this.build_drop_and_replace(
                        block, lhs_span, lhs, rhs
                    ));
                    block.unit()
                } else {
                    let rhs = unpack!(block = this.as_rvalue(block, rhs));
                    let lhs = unpack!(block = this.as_lvalue(block, lhs));
                    this.cfg.push_assign(block, source_info, &lhs, rhs);
                    block.unit()
                }
            }
            ExprKind::AssignOp { op, lhs, rhs } => {
                // FIXME(#28160) there is an interesting semantics
                // question raised here -- should we "freeze" the
                // value of the lhs here?  I'm inclined to think not,
                // since it seems closer to the semantics of the
                // overloaded version, which takes `&mut self`.  This
                // only affects weird things like `x += {x += 1; x}`
                // -- is that equal to `x + (x + 1)` or `2*(x+1)`?

                let lhs = this.hir.mirror(lhs);
                let lhs_ty = lhs.ty;

                // As above, RTL.
                let rhs = unpack!(block = this.as_operand(block, rhs));
                let lhs = unpack!(block = this.as_lvalue(block, lhs));

                // we don't have to drop prior contents or anything
                // because AssignOp is only legal for Copy types
                // (overloaded ops should be desugared into a call).
                let result = unpack!(block = this.build_binary_op(block, op, expr_span, lhs_ty,
                                                  Operand::Consume(lhs.clone()), rhs));
                this.cfg.push_assign(block, source_info, &lhs, result);

                block.unit()
            }
            ExprKind::Continue { label } => {
                let LoopScope { continue_block, extent, .. } =
                    *this.find_loop_scope(expr_span, label);
                this.exit_scope(expr_span, extent, block, continue_block);
                this.cfg.start_new_block().unit()
            }
            ExprKind::Break { label, value } => {
                let (break_block, extent, destination) = {
                    let LoopScope {
                        break_block,
                        extent,
                        ref break_destination,
                        ..
                    } = *this.find_loop_scope(expr_span, label);
                    (break_block, extent, break_destination.clone())
                };
                if let Some(value) = value {
                    unpack!(block = this.into(&destination, block, value))
                } else {
                    this.cfg.push_assign_unit(block, source_info, &destination)
                }
                this.exit_scope(expr_span, extent, block, break_block);
                this.cfg.start_new_block().unit()
            }
            ExprKind::Return { value } => {
                block = match value {
                    Some(value) => {
                        unpack!(this.into(&Lvalue::Local(RETURN_POINTER), block, value))
                    }
                    None => {
                        this.cfg.push_assign_unit(block,
                                                  source_info,
                                                  &Lvalue::Local(RETURN_POINTER));
                        block
                    }
                };
                let extent = this.extent_of_return_scope();
                let return_block = this.return_block();
                this.exit_scope(expr_span, extent, block, return_block);
                this.cfg.start_new_block().unit()
            }
            ExprKind::Become { value } =>
                return this.build_become(block, value, source_info),
            _ => {
                let expr_ty = expr.ty;
                let temp = this.temp(expr.ty.clone());
                unpack!(block = this.into(&temp, block, expr));
                unpack!(block = this.build_drop(block, expr_span, temp, expr_ty));
                block.unit()
            }
        }
    }

}
