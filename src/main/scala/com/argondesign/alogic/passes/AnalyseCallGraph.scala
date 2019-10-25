////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Peter de Rivaz/Geza Lore
//
// DESCRIPTION:
//
// Analyse call graph and:
//  - Check reclimit attributes
//  - Ensure reclimit attributes exist on all functions
//  - Check stacklimit attributes
//  - Allocate return stack with required depth
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.StatefulTreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FuncVariant
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.lib.Matrix
import com.argondesign.alogic.typer.TypeAssigner
import com.argondesign.alogic.util.unreachable

import scala.annotation.tailrec
import scala.collection.mutable

final class AnalyseCallGraph(implicit cc: CompilerContext) extends StatefulTreeTransformer {

  //////////////////////////////////////////////////////////////////////////
  // State for collecting information in the enter section
  //////////////////////////////////////////////////////////////////////////

  // Current function we are inside of
  private[this] var currentFunction: Symbol = _

  // Set of caller -> callee call arcs. Caller is option because "None" represents "Universe which calls main".
  private[this] val callArcs = mutable.Set.empty[(Option[Symbol], Symbol)]

  // Map of number of times each function is called
  private[this] val callCounts = mutable.Map[Symbol, Int]().withDefaultValue(0)

  // Set of caller -> callee goto arcs
  private[this] val gotoArcs = mutable.Set.empty[(Symbol, Symbol)]

  // All function symbols
  private[this] var functionSymbols: List[Symbol] = _

  //////////////////////////////////////////////////////////////////////////
  // Lazy vals used for computation in the transform section
  //////////////////////////////////////////////////////////////////////////

  // number of function symbols
  private[this] lazy val nFunctions = functionSymbols.length

  //////////////////////////////////////////////////////////////////////////////
  // All callGoto arcs in the entity
  //
  // Goto arcs are treated as proper tail calls, i.e.: as calls from the
  // caller of the function executing the goto to the target of the goto.
  // To do this we transitively propagate goto arcs as call arcs from all
  // functions that call the source of the goto to the target of the goto:
  //   a --call--> b --goto--> c
  // is treated as
  //   a --call--> {b, c}
  // or in a more general case:
  //   {a,b} --call--> {c, d} --goto--> {e, f}
  // is treated as
  //   {a, b} --call--> {c, d, e, f}
  // We store each arc as a triple, (caller, firstCallee, callee), e.g.
  //   a --call--> b             is stored as (a,b,b)
  //   a --call--> b --goto--> c is stored as (a,b,c)
  //////////////////////////////////////////////////////////////////////////////
  private[this] lazy val callGotoArcSet = if (callArcs.isEmpty) {
    // As an optimization, if we know that there are no calls, then
    // we know that there won't be any after goto conversion either
    Set.empty[(Option[Symbol], Symbol, Symbol)]
  } else {

    val arcsSoFar: mutable.Set[(Option[Symbol], Symbol, Symbol)] = {
      callArcs map {
        case (caller, callee) => (caller, callee, callee)
      }
    }

    // Set of all callers of callee based on the current arcsSoFar
    // This is forced to an immutable set to avoid iterating arcsSoFar
    // while it is being modified in the for expression below
    def callersAndFirstCallees(callee: Symbol) = {
      (arcsSoFar filter { _._3 == callee } map {
        case (caller, firstCallee, _) => (caller, firstCallee)
      }).toSet
    }

    @tailrec
    def gatherGotoArcs(): Unit = {
      val arcsSoFarSizeBeforeComb = arcsSoFar.size

      for {
        (intermediate, callee) <- gotoArcs
        (caller, firstCallee) <- callersAndFirstCallees(intermediate)
      } {
        arcsSoFar add ((caller, firstCallee, callee))
      }

      // Continue until we've found every callGoto arc
      if (arcsSoFar.size > arcsSoFarSizeBeforeComb) {
        gatherGotoArcs()
      }
    }

    gatherGotoArcs()
    arcsSoFar.toSet
  }

  //////////////////////////////////////////////////////////////////////////////
  // Adjacency matrix of the callGoto graph
  //////////////////////////////////////////////////////////////////////////////
  private[this] lazy val adjMat: Matrix[Int] = Matrix {
    val calleeMap = callGotoArcSet.groupMap(_._1)(_._3) withDefaultValue Set.empty
    for (caller <- functionSymbols) yield {
      val calleeSet = calleeMap(Some(caller))
      for (symbol <- functionSymbols) yield {
        if (calleeSet contains symbol) 1 else 0
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Indirect connectivity matrix of the call graph
  //
  // Compute the indirect matrix by summing over all powers of the adjacency
  // matrix between 2 and nFunctions. This will have a non-zero on the diagonal
  // if the function is recursively entered through a cycle of any length >= 2
  //////////////////////////////////////////////////////////////////////////////
  private[this] lazy val indMat: Matrix[Int] = {
    if (nFunctions == 1) {
      Matrix.zeros[Int](1)
    } else {
      @tailrec
      def loop(pow: Int, curr: Matrix[Int], acc: Matrix[Int]): Matrix[Int] = {
        if (pow == 2) {
          acc
        } else {
          val prod = curr * adjMat
          loop(pow - 1, prod, prod + acc)
        }
      }

      val square = adjMat * adjMat
      loop(nFunctions, square, square)
    }
  }

  private[this] def warnIgnoredStacklimitAttribute(eSymbol: Symbol): Unit = {
    if (eSymbol.attr.stackLimit.isSet) {
      val loc = eSymbol.loc
      val name = eSymbol.name
      cc.warning(loc, s"'stacklimit' attribute ignored on entity '${name}'")
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Collect 'reclimit' values and check that they are sensible
  //////////////////////////////////////////////////////////////////////////////
  private[this] lazy val recLimits: Option[List[Int]] = {
    val directlyRecursive = adjMat.diagonal map { _ != 0 }
    val indirectlyRecursive = indMat.diagonal map { _ != 0 }

    val list = List from {
      for {
        (symbol, isRecD, isRecI) <- functionSymbols lazyZip directlyRecursive lazyZip indirectlyRecursive
      } yield {
        lazy val loc = symbol.loc
        lazy val name = symbol.name
        val exprOpt = symbol.attr.recLimit.get
        if (!isRecD && !isRecI) {
          if (exprOpt.isDefined) {
            cc.warning(loc, s"'reclimit' attribute ignored on function '${name}'")
          }
          1
        } else {
          exprOpt match {
            case None => {
              val hint = if (isRecD) "Recursive" else "Indirectly recursive"
              cc.error(loc, s"${hint} function '${name}' requires 'reclimit' attribute")
              0
            }
            case Some(expr) => {
              expr.value match {
                case Some(value) if value < 2 => {
                  cc.error(
                    loc,
                    s"Recursive function '${name}' has 'reclimit' attribute equal to ${value}"
                  )
                  0
                }
                case None => {
                  symbol.attr.recLimit set Expr(2)
                  cc.error(loc,
                           s"Cannot compute value of 'reclimit' attribute of function '${name}'")
                  0
                }
                case Some(value) => value.toInt
              }
            }
          }
        }
      }
    }

    // 0 is only possible if there was an error so yield None in that case
    if (list contains 0) None else Some(list)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Computes the length of the longest static path in the call graphs
  //////////////////////////////////////////////////////////////////////////////
  private[this] def computeLongestPathLength(costOfCalling: Map[Symbol, Int]): Int = {
    // Find the longest simple (non-cyclic) path in the call graph
    // Note strictly this is only an upper bound on the required
    // return stack depth if there is recursion
    val (length, _) = {
      // Longest path from 'node' that goes through only vertices that are in 'nodes'
      def longestPathFrom(node: Option[Symbol], nodes: Set[Symbol]): (Int, List[Symbol]) = {
        assert(node == None || !(nodes contains node.get))
        // Candidate successors are the vertices which are callees of this node and are in 'nodes'
        val candidates = callGotoArcSet collect {
          case (caller, firstCallee, callee) if (caller == node) && (nodes contains callee) =>
            (firstCallee, callee)
        }
        // Find longest paths from each of these candidates
        val paths = for ((firstCallee, callee) <- candidates) yield {
          val (l, p) = longestPathFrom(Some(callee), nodes - callee)
          (firstCallee, l, p)
        }

        if (paths.isEmpty) {
          // If no further paths, we are done
          (0, node.toList)
        } else {
          // Find the one that is the longest among all candidates
          val (firstCallee, len, longest) = paths maxBy {
            case (fc, l, _) => costOfCalling(fc) + l
          }
          // Prepend this node
          (costOfCalling(firstCallee) + len, node.toList ::: longest)
        }
      }

      val funcSet = functionSymbols.toSet

      // Get the longest path originating from "None", which represents "the universe which calls main"
      longestPathFrom(None, funcSet)

    }

    length
  }

  //
  // If the return point of this function is known at compile time, Some(functionCall).
  // Otherwise, None. E.g. If the only callGotoArc ending at c is (a,b,c), (and b is only called
  // once within the body of a) then the unique return point is Some(b).
  // If no callGotoArcs end at c then return to the top of main.
  //
  private[this] lazy val uniqueReturnPoint: Map[Symbol, Option[Symbol]] = {
    Map from (for (sym <- functionSymbols) yield {
      val firstCalleesOfCallee = callGotoArcSet filter { _._3 == sym } map { _._2 }
      firstCalleesOfCallee.toList match {
        case List(uniqueFirstCallee) =>
          sym -> (if (callCounts(uniqueFirstCallee) == 1) Some(uniqueFirstCallee) else None)
        case _ =>
          assert(firstCalleesOfCallee.nonEmpty)
          sym -> None
      }
    })
  }

  //
  // When this function is called, should we push an entry to the return stack. True if and only if
  // every callGotoArc with this function as firstCallee ends at a function with uniqueReturnPoint
  //
  private[this] lazy val pushStackOnCall: Map[Symbol, Boolean] = {
    Map from (for (sym <- functionSymbols) yield {
      if (callCounts(sym) > 1) {
        // Optimization if this function is called more than once
        sym -> true
      } else {
        val callGotoArcsWithSymAsFirstCallee = callGotoArcSet filter { _._2 == sym }
        // Since callCounts(sym) == 1, all tuples should have identical callers (first tuple item).
        assert(callGotoArcsWithSymAsFirstCallee forall {
          _._1 == callGotoArcsWithSymAsFirstCallee.head._1
        })
        val noNeedToPushToStack = callGotoArcsWithSymAsFirstCallee forall {
          case (_, _, callee) =>
            val urp = uniqueReturnPoint(callee)
            urp.isDefined tap {
              if (_) assert(urp.get == sym) // The unique return point should be exactly this symbol
            }
        }
        sym -> !noNeedToPushToStack
      }
    })
  }

  //////////////////////////////////////////////////////////////////////////////
  // The actual return stack depth required
  //////////////////////////////////////////////////////////////////////////////
  private[this] def returnStackDepth(eSymbol: Symbol): Int = {
    // Compute if the entity uses any recursion
    val hasRecursion = adjMat.diagonal.sum + indMat.diagonal.sum != 0

    // Issue ignored attribute waring if required
    if (!hasRecursion) {
      warnIgnoredStacklimitAttribute(eSymbol)
    }

    // Compute the value of the 'stacklimit' attribute of the entity
    lazy val stackLimit: Option[Int] = {
      eSymbol.attr.stackLimit.get flatMap { expr =>
        lazy val loc = eSymbol.loc
        lazy val name = eSymbol.name
        expr.value match {
          case Some(value) if value < 1 =>
            cc.error(loc, s"Entity '$name' has 'stacklimit' attribute equal to $value")
            None
          case None =>
            cc.error(loc, s"Cannot compute value of 'stacklimit' attribute of entity '$name'")
            None
          case Some(value) => Some(value.toInt)
        }
      }
    }

    // Compute the maximum number of pushes to stack
    if (hasRecursion && stackLimit.isDefined) {
      // If the entity uses recursion and has a sane
      // 'stacklimit' attribute, use the value of that.
      // We subtract one as the root function does not return anywhere
      stackLimit.get - 1
    } else {
      recLimits map { weights =>
        val costs = (functionSymbols lazyZip weights) map {
          case (firstCallee, recLimit) =>
            if (pushStackOnCall(firstCallee)) recLimit else 0
        }

        // Map from symbol -> max stack pushs for this function
        val costOfCalling = Map from (functionSymbols zip costs)

        // Find the longest path in the static call graph
        computeLongestPathLength(costOfCalling)
      } getOrElse {
        // If we don't have sane recLimits, emit a return stack of size 1
        1
      }
    }
  }

  override protected def skip(tree: Tree): Boolean = tree match {
    case decl: DeclEntity                                               => decl.functions.isEmpty
    case DefnEntity(symbol, variant, _) if variant != EntityVariant.Fsm =>
      // Warn early if there are no functions at all, as
      // we will not have an opportunity to do it later
      warnIgnoredStacklimitAttribute(symbol)
      true
    case _: DefnEntity => false
    case _: EntDefn    => false
    case _: Ent        => true
    case _: DefnFunc   => false
    case _: Defn       => true
    case _: Decl       => true
    case _             => false
  }

  override def enter(tree: Tree): Option[Tree] = tree match {

    //////////////////////////////////////////////////////////////////////////
    // Gather all function symbols defined in the
    //////////////////////////////////////////////////////////////////////////

    case defn: DefnEntity =>
      assert(functionSymbols == null)
      functionSymbols = defn.functions map { _.symbol }
      val entryPoints = functionSymbols filter { _.attr.entry.isSet }
      Option.when(entryPoints.lengthIs != 1) {
        if (entryPoints.isEmpty) {
          cc.error(defn.symbol, "No 'main' function in fsm.")
        } else {
          val locations = entryPoints map { _.loc.prefix }
          cc.error(defn.symbol, "Multiple 'main' functions in fsm at:" :: locations: _*)
        }
        tree
      }

    //////////////////////////////////////////////////////////////////////////
    // Note current function we are processing
    //////////////////////////////////////////////////////////////////////////

    case defn: DefnFunc =>
      currentFunction = defn.symbol
      if (currentFunction.name == "main") {
        // Add a call arc from the "Universe which calls main" to the start of main.
        callArcs add (None -> currentFunction)
        callCounts(currentFunction) += 1
      }
      None

    //////////////////////////////////////////////////////////////////////////
    // Collect the call graph edges as we go
    //////////////////////////////////////////////////////////////////////////

    case ExprCall(ref, _) if ref.tpe.isCtrlFunc =>
      ref match {
        case ExprSym(callee) =>
          callArcs add (Some(currentFunction) -> callee)
          callCounts(callee) += 1
        case _ => unreachable
      }
      None

    case StmtGoto(ExprSym(callee)) =>
      gotoArcs add (currentFunction -> callee)
      None

    //
    case _ => None

  }

  override def transform(tree: Tree): Tree = tree match {
    case defn: DefnEntity =>
      // Ensure 'reclimit' attributes exist on all functions
      val values = recLimits.getOrElse(List.fill(nFunctions)(1))
      for ((symbol, value) <- functionSymbols zip values) {
        symbol.attr.recLimit set Expr(value)
      }

      // Set function attribute pushStackOnCall
      for { symbol <- functionSymbols } {
        symbol.attr.pushStackOnCall set pushStackOnCall(symbol)
      }

      // Set function attributes staticReturnPoint and popStackOnReturn
      for { symbol <- functionSymbols } {
        symbol.attr.staticReturnPoint set uniqueReturnPoint(symbol)

        symbol.attr.popStackOnReturn set {
          uniqueReturnPoint(symbol) match {
            case Some(firstCallee) => pushStackOnCall(firstCallee)
            case None              => true
          }
        }
      }

      val stackDepth = returnStackDepth(defn.symbol)

      if (stackDepth == 0) {
        defn
      } else {
        // Allocate the return stack with TypeVoid entries and with the right
        // depth. The elementType will be refined in a later pass when the
        // state numbers are allocated
        val name = if (stackDepth > 1) "return_stack" else "return_state"
        val symbol = cc.newSymbol(name, defn.loc) tap { s =>
          s.kind = TypeStack(TypeVoid, stackDepth)
          s.attr.returnStack set true
        }
        // Add th Defn of the return stack. ConvertControl relies on it being
        // added to the front so it can be picked up in 'transform' early.
        val stackDefn = EntDefn(symbol.mkDefn) regularize defn.loc
        TypeAssigner(defn.copy(body = stackDefn :: defn.body) withLoc defn.loc)
      }

    case decl: DeclEntity =>
      decl.symbol.defn.defns collectFirst {
        // Add the Decl of the return stack
        case Defn(symbol) if symbol.attr.returnStack.isSet =>
          val stackDecl = symbol.mkDecl regularize decl.loc
          TypeAssigner(decl.copy(decls = stackDecl :: decl.decls) withLoc decl.loc)
      } getOrElse tree

    case _ => tree
  }

  override def finalCheck(tree: Tree): Unit = tree visit {
    case node: Tree if !node.hasTpe => cc.ice(node, "Lost tpe of", node.toString)
    case node @ DeclFunc(caller, FuncVariant.Ctrl, _, _) if !caller.attr.staticReturnPoint.isSet =>
      cc.ice(node, "Function with attribute staticReturnPoint not set remains", node.toString)
    case node @ DeclFunc(caller, FuncVariant.Ctrl, _, _) if !caller.attr.popStackOnReturn.isSet =>
      cc.ice(node, "Function with attribute popStackOnReturn not set remains", node.toString)
    case node @ ExprCall(ref @ ExprSym(callee), _)
        if ref.tpe.isCtrlFunc && !callee.attr.pushStackOnCall.isSet =>
      cc.ice(node, "Function call with attribute pushStackOnCall not set remains", node.toString)
  }
}

object AnalyseCallGraph extends EntityTransformerPass(declFirst = false) {
  val name = "analyse-call-graph"

  def create(symbol: Symbol)(implicit cc: CompilerContext) = new AnalyseCallGraph
}
