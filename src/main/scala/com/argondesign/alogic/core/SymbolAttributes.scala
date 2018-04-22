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
// Collection of all symbol attributes
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.core

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.util.unreachable

class SymbolAttributes {
  // Is this an entry point function
  val entry = new Attribute[Boolean]()

  // All possible parameter bindings of an entity symbol
  val paramBindings = new Attribute[List[Map[TermSymbol, Option[Expr]]]]()
  // The actual parameter bindings of an instance symbol
  val paramBinding = new Attribute[Map[TermSymbol, Option[Expr]]]()
  // If this is a parametrized entity symbol,
  // a map from parameter bindings to the specialized entity
  val specMap = new Attribute[Map[Map[TermSymbol, Option[Expr]], Entity]]()

  // Entity call stack limit
  val stackLimit = new Attribute[Expr]()
  // Function recursion limit
  val recLimit = new Attribute[Expr]()
  // The return stack symbol, if this is an entity
  val returnStack = new Attribute[TermSymbol]()
  // The state variable symbol, if this is an entity
  val stateVar = new Attribute[TermSymbol]()

  // Is this a FlowControlTypeNone port?
  val fcn = new Attribute[Boolean]()
  // If this is a FlowControlTypeValid port,
  // the corresponding payload and valid symbols
  val fcv = new Attribute[(Symbol, TermSymbol)]()
  // If this is a FlowControlTypeReady port,
  // the corresponding payload, valid and ready symbols
  val fcr = new Attribute[(Symbol, TermSymbol, TermSymbol)]()
  // If this is a FlowControlTypeAccept port,
  // the corresponding payload, valid and accept symbols
  val fca = new Attribute[(Symbol, TermSymbol, TermSymbol)]()
  // If this is an output port with StorageTypeSlices, the
  // corresponding output slice entity and instance symbol
  val oSlice = new Attribute[(Entity, TermSymbol)]()
  // Is this a port that has been expanded to multiple signals?
  val expandedPort = new Attribute[Boolean]()

  // The expanded field symbols of a struct symbol
  val fieldSymbols = new Attribute[List[TermSymbol]]()

  // Iterator that enumerates all fields above
  private def attrIterator = Iterator(
    entry,
    paramBinding,
    paramBinding,
    specMap,
    stackLimit,
    recLimit,
    returnStack,
    stateVar,
    fcn,
    fcv,
    fcr,
    fca,
    oSlice,
    expandedPort,
    fieldSymbols
  )

  // Iterator that enumerates names of fields above
  private def nameIterator = Iterator(
    "entry",
    "paramBinding",
    "paramBinding",
    "specMap",
    "stackLimit",
    "recLimit",
    "returnStack",
    "stateVar",
    "fcn",
    "fcv",
    "fcr",
    "fca",
    "oSlice",
    "expandedPor",
    "fieldSymbols"
  )

  // Copy values of attributes from another instance
  def update(that: SymbolAttributes): Unit = {
    for ((a, b) <- attrIterator zip that.attrIterator) {
      a.asInstanceOf[Attribute[Any]] update b.asInstanceOf[Attribute[Any]]
    }
  }

  // Copy values from source attributes
  def update(that: SourceAttributes): Unit = if (that.hasAttr) {
    for ((name, expr) <- that.attr) {
      name match {
        case "stacklimit" => stackLimit set expr
        case "reclimit"   => recLimit set expr
        case _            => unreachable
      }
    }
  }

  // Render in some human readable form
  def toSource(implicit cc: CompilerContext): String = {
    val parts = for ((name, attr) <- nameIterator zip attrIterator if attr.isSet) yield {
      attr.value match {
        case true       => s"${name}"
        case false      => s"!${name}"
        case expr: Expr => s"${name} = ${expr.toSource}"
        case other      => s"${name} = ${other.toString}"
      }
    }
    if (parts.nonEmpty) parts.mkString("(* ", ", ", " *)") else ""
  }
}