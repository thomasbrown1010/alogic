////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018-2020 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// - Lower stack variables into stack instances
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.StatefulTreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.StackFactory
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.Types.TypeStack
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.util.unreachable

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

final class LowerStacks(implicit cc: CompilerContext) extends StatefulTreeTransformer {

  // Map from original stack variable symbol to the
  // corresponding stack entity and instance symbols
  private[this] val stackMap = mutable.LinkedHashMap[Symbol, ((DeclEntity, DefnEntity), Symbol)]()

  // Stack of extra statements to emit when finished with a statement
  private[this] val extraStmts = mutable.Stack[mutable.ListBuffer[Stmt]]()

  override def enter(tree: Tree): Option[Tree] = {
    tree match {
      case Decl(symbol) =>
        symbol.kind match {
          case TypeStack(kind, depth) =>
            // Construct the stack entity
            val loc = tree.loc
            val pName = symbol.name
            // TODO: mark inline
            val eName = entitySymbol.name + cc.sep + "stack" + cc.sep + pName
            val stackEntity = StackFactory(eName, loc, kind, depth)
            val instanceSymbol = cc.newSymbol(pName, loc) tap {
              _.kind = stackEntity._1.symbol.kind.asType.kind
            }
            stackMap(symbol) = (stackEntity, instanceSymbol)
            // Clear enable when the entity stalls
            entitySymbol.attr.interconnectClearOnStall.append((instanceSymbol, "en"))

          case _ =>
        }

      case _: Stmt =>
        // Whenever we enter a new statement, add a new buffer to
        // store potential extra statements
        extraStmts.push(ListBuffer())

      case _ =>
    }
    None
  }

  private[this] def assignTrue(expr: Expr) = StmtAssign(expr, ExprInt(false, 1, 1))
  private[this] def assignFalse(expr: Expr) = StmtAssign(expr, ExprInt(false, 1, 0))

  override def transform(tree: Tree): Tree = {
    val result: Tree = tree match {

      //////////////////////////////////////////////////////////////////////////
      // Rewrite statements
      //////////////////////////////////////////////////////////////////////////

      case StmtExpr(ExprCall(ExprSelect(ExprSym(symbol), "push", _), List(ArgP(arg)))) =>
        stackMap.get(symbol) map {
          case (_, iSymbol) =>
            StmtBlock(
              List(
                assignTrue(ExprSym(iSymbol) select "en"),
                assignTrue(ExprSym(iSymbol) select "push"),
                StmtAssign(ExprSym(iSymbol) select "d", arg)
              ))
        } getOrElse {
          tree
        }

      case StmtExpr(ExprCall(ExprSelect(ExprSym(symbol), "set", _), List(ArgP(arg)))) =>
        stackMap.get(symbol) map {
          case (_, iSymbol) =>
            StmtBlock(
              List(
                assignTrue(ExprSym(iSymbol) select "en"),
                StmtAssign(ExprSym(iSymbol) select "d", arg)
              ))

        } getOrElse {
          tree
        }

      //////////////////////////////////////////////////////////////////////////
      // Rewrite expressions
      //////////////////////////////////////////////////////////////////////////

      case ExprCall(ExprSelect(ExprSym(symbol), "pop", _), Nil) =>
        stackMap.get(symbol) map {
          case (_, iSymbol) =>
            extraStmts.top append assignTrue(ExprSym(iSymbol) select "en")
            extraStmts.top append assignTrue(ExprSym(iSymbol) select "pop")
            ExprSym(iSymbol) select "q"
        } getOrElse {
          tree
        }

      case ExprSelect(ExprSym(symbol), "top", _) =>
        stackMap.get(symbol) map {
          case (_, iSymbol) => ExprSym(iSymbol) select "q"
        } getOrElse {
          tree
        }

      case ExprSelect(ExprSym(symbol), "full", _) =>
        stackMap.get(symbol) map {
          case (_, iSymbol) => ExprSym(iSymbol) select "full"
        } getOrElse {
          tree
        }

      case ExprSelect(ExprSym(symbol), "empty", _) =>
        stackMap.get(symbol) map {
          case (_, iSymbol) => ExprSym(iSymbol) select "empty"
        } getOrElse {
          tree
        }

      //////////////////////////////////////////////////////////////////////////
      // Replace Stack Decl/Defn with the Decl/Defn of the expanded symbols
      //////////////////////////////////////////////////////////////////////////

      case DeclStack(symbol, _, _) => stackMap(symbol)._2.mkDecl

      case DefnStack(symbol) => stackMap(symbol)._2.mkDefn

      //////////////////////////////////////////////////////////////////////////
      // Add stack connections
      //////////////////////////////////////////////////////////////////////////

      case defn: DefnEntity if stackMap.nonEmpty =>
        val newBody = List from {
          // Drop the comb process
          defn.body.iterator filter {
            case _: EntCombProcess => false
            case _                 => true
          } concat {
            Iterator single {
              // Add leading statements to the state system
              assert(defn.combProcesses.lengthIs <= 1)

              val leading = stackMap.values map {
                _._2
              } map { iSymbol =>
                val iRef = ExprSym(iSymbol)
                StmtBlock(
                  List(
                    assignFalse(iRef select "en"),
                    StmtAssign(iRef select "d", iRef select "q"), // TODO: redundant
                    assignFalse(iRef select "push"), // TODO: redundant
                    assignFalse(iRef select "pop") // TODO: redundant
                  )
                )
              }

              defn.combProcesses.headOption map {
                case EntCombProcess(stmts) => EntCombProcess(List.concat(leading, stmts))
              } getOrElse {
                EntCombProcess(leading.toList)
              }
            }
          }
        }

        defn.copy(body = newBody)

      //
      case _ => tree
    }

    // Emit any extra statement with this statement
    val result2 = result match {
      case stmt: Stmt =>
        val extra = extraStmts.pop()
        if (extra.isEmpty) stmt else StmtBlock((extra append stmt).toList)
      case _ => result
    }

    // If we did modify the node, regularize it
    if (result2 ne tree) {
      result2 regularize tree.loc
    }

    // Done
    result2
  }

  override def finish(tree: Tree): Tree = tree match {
    case _: DeclEntity => Thicket(tree :: List.from(stackMap.valuesIterator map { _._1._1 }))
    case _: DefnEntity => Thicket(tree :: List.from(stackMap.valuesIterator map { _._1._2 }))
    case _             => unreachable
  }
  override def finalCheck(tree: Tree): Unit = {
    assert(extraStmts.isEmpty)

    tree visit {
      case node @ ExprSelect(ref, sel, _) if ref.tpe.isStack => cc.ice(node, s"Stack .$sel remains")
    }
  }

}

object LowerStacks extends PairTransformerPass {
  val name = "lower-stacks"
  def transform(decl: Decl, defn: Defn)(implicit cc: CompilerContext): (Tree, Tree) = {
    (decl, defn) match {
      case (dcl: DeclEntity, dfn: DefnEntity) =>
        if (dcl.decls.isEmpty || dfn.variant == EntityVariant.Net) {
          // If no decls, or network, then there is nothing to do
          (decl, defn)
        } else {
          // Perform the transform
          val transformer = new LowerStacks
          // First transform the decl
          val newDecl = transformer(decl)
          // Then transform the defn
          val newDefn = transformer(defn)
          (newDecl, newDefn)
        }
      case _ => (decl, defn)
    }
  }
}
