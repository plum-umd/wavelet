//! Ghost expression checking.

use crate::ghost::ir::{GhostExpr, GhostStmt};

use super::context::CheckContext;
use super::pretty_print::{
    print_context_contents, render_ghost_stmt, render_ghost_tail, trace_context,
};
use super::stmt_checker::*;
use super::tail_checker::*;

pub fn check_ghost_expr(expr: &GhostExpr, ctx: &mut CheckContext) -> Result<(), String> {
    let stmts = &expr.stmts;
    let mut i = 0;

    trace_context(ctx, "Entering ghost expression");

    while i < stmts.len() {
        match &stmts[i] {
            GhostStmt::Pure { .. } => {
                // Pure statements stand alone
                if ctx.verbose {
                    println!(
                        "Processing statement {}: {}",
                        i,
                        render_ghost_stmt(&stmts[i])
                    );
                }
                check_ghost_stmt_pure(&stmts[i], ctx)?;
                if ctx.verbose {
                    println!("After Pure statement:");
                    print_context_contents(ctx);
                }
                i += 1;
            }
            GhostStmt::JoinSplit { .. } => {
                // JoinSplit must be followed by another statement or tail
                if i + 1 >= stmts.len() {
                    // This is the last statement, so it must precede a tail (Return)
                    if ctx.verbose {
                        println!(
                            "JoinSplit at end, checking with tail: {}",
                            render_ghost_tail(&expr.tail)
                        );
                    }
                    check_ghost_tail_with_joinsplit(&stmts[i], &expr.tail, ctx)?;
                    if ctx.verbose {
                        println!("After JoinSplit+Return:");
                        print_context_contents(ctx);
                    }
                    return Ok(());
                }

                match &stmts[i + 1] {
                    GhostStmt::Const { .. } => {
                        // JoinSplit followed by Const
                        if ctx.verbose {
                            println!(
                                "Processing statement {}: {}",
                                i,
                                render_ghost_stmt(&stmts[i + 1])
                            );
                        }
                        check_ghost_stmt_joinsplit_const(&stmts[i], &stmts[i + 1], ctx)?;
                        if ctx.verbose {
                            println!("After JoinSplit+Const:");
                            print_context_contents(ctx);
                        }
                        i += 2;
                    }
                    GhostStmt::Load { .. } => {
                        // JoinSplit followed by Load
                        if ctx.verbose {
                            println!(
                                "Processing statement {}: {}",
                                i,
                                render_ghost_stmt(&stmts[i + 1])
                            );
                        }
                        check_ghost_stmt_joinsplit_load(&stmts[i], &stmts[i + 1], ctx)?;
                        if ctx.verbose {
                            println!("After JoinSplit+Load:");
                            print_context_contents(ctx);
                        }
                        i += 2;
                    }
                    GhostStmt::Store { .. } => {
                        // JoinSplit followed by Store
                        if ctx.verbose {
                            println!(
                                "Processing statement {}: {}",
                                i,
                                render_ghost_stmt(&stmts[i + 1])
                            );
                        }
                        check_ghost_stmt_joinsplit_store(&stmts[i], &stmts[i + 1], ctx)?;
                        if ctx.verbose {
                            println!("After JoinSplit+Store:");
                            print_context_contents(ctx);
                        }
                        i += 2;
                    }
                    GhostStmt::JoinSplit { .. } => {
                        // Two JoinSplits must be followed by Call or tail
                        if i + 2 >= stmts.len() {
                            // The two JoinSplits are the last statements, so
                            // they must precede a tail (Call)
                            if ctx.verbose {
                                println!(
                                    "Two JoinSplits at end, checking with tail: {}",
                                    render_ghost_tail(&expr.tail)
                                );
                            }
                            check_ghost_tail_with_two_joinsplits(
                                &stmts[i],
                                &stmts[i + 1],
                                &expr.tail,
                                ctx,
                            )?;
                            if ctx.verbose {
                                println!("After JoinSplit+JoinSplit+TailCall:");
                                print_context_contents(ctx);
                            }
                            return Ok(());
                        }
                        match &stmts[i + 2] {
                            GhostStmt::Call { .. } => {
                                // Two JoinSplits followed by Call
                                if ctx.verbose {
                                    println!(
                                        "Processing statement {}: {}",
                                        i,
                                        render_ghost_stmt(&stmts[i + 2])
                                    );
                                }
                                check_ghost_stmt_jnsplt_jnsplt_call(
                                    &stmts[i],
                                    &stmts[i + 1],
                                    &stmts[i + 2],
                                    ctx,
                                )?;
                                if ctx.verbose {
                                    println!("After JoinSplit+JoinSplit+Call:");
                                    print_context_contents(ctx);
                                }
                                i += 3;
                            }
                            _ => {
                                return Err(format!(
                                    "Two JoinSplits must be followed by Call or TailCall, found {:?}",
                                    stmts[i + 2]
                                ));
                            }
                        }
                    }
                    _ => {
                        return Err(format!(
                            "Invalid statement sequence: JoinSplit followed by {:?}",
                            stmts[i + 1]
                        ));
                    }
                }
            }
            _ => {
                return Err(format!(
                    "Statement {:?} must be preceded by JoinSplit",
                    stmts[i]
                ));
            }
        }
    }

    // If no more statements, check the tail if-else
    if ctx.verbose {
        println!("Checking tail: {}", render_ghost_tail(&expr.tail));
    }
    check_ghost_tail_if(&expr.tail, ctx)?;
    if ctx.verbose {
        println!("After tail:");
        print_context_contents(ctx);
    }
    Ok(())
}
