////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Build a Stmt AST from an Antlr4 parse tree
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.antlr

import com.argondesign.alogic.antlr.AlogicParser._
import com.argondesign.alogic.antlr.AntlrConverters._
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import org.antlr.v4.runtime.ParserRuleContext

import scala.jdk.CollectionConverters._

object StmtBuilder extends BaseBuilder[ParserRuleContext, Stmt] {

  private def makeStmtList(stmt: Stmt): List[Stmt] = stmt match {
    case StmtBlock(ss) => ss
    case s             => List(s)
  }

  def apply(ctx: ParserRuleContext)(implicit cc: CompilerContext): Stmt = {
    object Visitor extends AlogicScalarVisitor[Stmt] { self =>
      // Block
      override def visitBlock(ctx: BlockContext) = {
        StmtBlock(visit(ctx.statement)) withLoc ctx.loc
      }

      // Proxy nodes
      override def visitStatementAssignment(ctx: StatementAssignmentContext) = visit(ctx.assignment)
      override def visitStatementLoop(ctx: StatementLoopContext) = visit(ctx.loop)

      override def visitStmtDecl(ctx: StmtDeclContext) = {
        StmtDecl(DeclBuilder(ctx.decl)) withLoc ctx.loc
      }

      override def visitStmtAssign(ctx: StmtAssignContext) = {
        StmtAssign(ExprBuilder(ctx.expr(0)), ExprBuilder(ctx.expr(1))) withLoc {
          ctx.loc.copy(point = ctx.op.getStartIndex)
        }
      }

      override def visitStmtUpdate(ctx: StmtUpdateContext) = {
        StmtUpdate(ExprBuilder(ctx.expr(0)), ctx.ASSIGNOP.text.init, ExprBuilder(ctx.expr(1))) withLoc {
          ctx.loc.copy(point = ctx.ASSIGNOP.getStartIndex)
        }
      }

      override def visitStmtPost(ctx: StmtPostContext) = {
        StmtPost(ExprBuilder(ctx.expr), ctx.op) withLoc ctx.loc
      }

      override def visitStmtLet(ctx: StmtLetContext) = {
        val inits = visit(ctx.let.loop_init.loop_init_item)
        val loop = makeStmtList(visit(ctx.loop))
        StmtLet(inits, loop) withLoc ctx.loc
      }

      override def visitStmtLoop(ctx: StmtLoopContext) = {
        val body = visit(ctx.block.statement)
        StmtLoop(body) withLoc ctx.loc
      }

      override def visitStmtDo(ctx: StmtDoContext) = {
        val cond = ExprBuilder(ctx.expr)
        val body = visit(ctx.block.statement)
        StmtDo(cond, body) withLoc ctx.loc
      }

      override def visitStmtWhile(ctx: StmtWhileContext) = {
        val cond = ExprBuilder(ctx.expr)
        val body = visit(ctx.block.statement)
        StmtWhile(cond, body) withLoc ctx.loc
      }

      override def visitStmtFor(ctx: StmtForContext) = {
        val inits = if (ctx.loop_init != null) visit(ctx.loop_init.loop_init_item) else Nil
        val cond = Option(ctx.expr) map { ExprBuilder(_) }
        val step = if (ctx.for_steps != null) visit(ctx.for_steps.step) else Nil
        val body = visit(ctx.block.statement)
        StmtFor(inits, cond, step, body) withLoc ctx.loc
      }

      override def visitStmtGoto(ctx: StmtGotoContext) = {
        val ref = ExprRef(IdentBuilder(ctx.ident)) withLoc ctx.ident.loc
        StmtGoto(ref) withLoc ctx.loc
      }

      override def visitStmtFence(ctx: StmtFenceContext) = {
        StmtFence() withLoc ctx.loc
      }

      override def visitStmtBreak(ctx: StmtBreakContext) = {
        StmtBreak() withLoc ctx.loc
      }

      override def visitStmtContinue(ctx: StmtContinueContext) = {
        StmtContinue() withLoc ctx.loc
      }

      override def visitStmtReturn(ctx: StmtReturnContext) = {
        StmtReturn() withLoc ctx.loc
      }

      override def visitStmtBlock(ctx: StmtBlockContext) = visit(ctx.block)

      override def visitStmtIf(ctx: StmtIfContext) = {
        val cond = ExprBuilder(ctx.expr)
        val thenStmts = makeStmtList(visit(ctx.thenStmt))
        val elseStmts = visit(Option(ctx.elseStmt)) map makeStmtList getOrElse Nil
        StmtIf(cond, thenStmts, elseStmts) withLoc ctx.loc
      }

      override def visitStmtCase(ctx: StmtCaseContext) = {
        val value = ExprBuilder(ctx.expr)
        val cases = ctx.case_clause.asScala.toList map { CaseBuilder(_) }
        StmtCase(value, cases) withLoc ctx.loc
      }

      override def visitStmtExpr(ctx: StmtExprContext) = {
        val stmt = ctx.expr.text match {
          case "read"  => StmtRead()
          case "write" => StmtWrite()
          case _       => StmtExpr(ExprBuilder(ctx.expr))
        }
        stmt withLoc ctx.loc
      }

      override def visitStmtGen(ctx: StmtGenContext): Stmt = {
        val gen = GenBuilder(ctx.generate)
        StmtGen(gen) withLoc ctx.loc
      }

      override def visitLoopInitAssign(ctx: LoopInitAssignContext) = {
        StmtAssign(ExprBuilder(ctx.expr(0)), ExprBuilder(ctx.expr(1))) withLoc ctx.loc
      }

      override def visitLoopInitDecl(ctx: LoopInitDeclContext) = {
        val ident = IdentBuilder(ctx.IDENTIFIER)
        val kind = TypeBuilder(ctx.kind)
        val init = ExprBuilder(ctx.expr)
        val decl = DeclRef(ident, kind, Some(init)) withLoc ctx.loc
        StmtDecl(decl) withLoc ctx.loc
      }
    }

    Visitor(ctx)
  }

}
