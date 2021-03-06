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
import com.argondesign.alogic.builtins.BuiltinPolyFunc
import com.argondesign.alogic.core.StorageTypes.StorageSlice
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.Types.TypeEntity

import scala.collection.mutable

class SymbolAttributes {
  // Symbol is meant to be unused, do not warn
  val unused = new Attribute[Boolean]()

  // Is this a toplevel entity
  val topLevel = new Attribute[Boolean]()
  // Is this an entry point function
  val entry = new Attribute[Boolean]()

  // Entity call stack limit
  val stackLimit = new Attribute[Expr]() // TODO: Treeify
  // Function recursion limit
  val recLimit = new Attribute[Expr]() // TODO: Treeify
  // This is the return stack of the enclosing entity
  val returnStack = new Attribute[Boolean]()
  // This is the go signal of the enclosing entity
  val go = new Attribute[Boolean]()

  // This is the clock signal of the enclosing entity
  val clk = new Attribute[Boolean]()
  // This is the reset signal of the enclosing entity
  val rst = new Attribute[Boolean]()

  // Back link to port this signal was created from
  val payloadOfPort = new Attribute[Symbol]()
  val validOfPort = new Attribute[Symbol]()
  val readyOfPort = new Attribute[Symbol]()

  // If this is an entity symbol, then the type it was before
  // flow control lowering and structure splitting (i.e.: with the high
  // level interface), without the TypeType wrapper
  val highLevelKind = new Attribute[TypeEntity]() // TODO: Treeify

  // If the state system stalls, set this signal to all zeros
  val clearOnStall = new Attribute[Boolean]()
  // If this is an entity symbol, then these are further (instance, portname)
  // pairs (driven from the state system) that need to be cleared on a stall
  val interconnectClearOnStall = new Attribute[List[(Symbol, String)]]() // TODO: Treeify

  // If the value of ExprSym(symbol) in this attribute is 0,
  // then the value of this signal is known to be don't care
  val dontCareUnless = new Attribute[Symbol]() // TODO: Treeify

  // Describes implication relationship between this symbol and the denoted
  // symbols. Both this symbol and the implied symbols must be 1 bit. There
  // are 2 further booleans attached. The first boolean denotes the state
  // of this, and the second boolean denotes the states of the attached symbol.
  // For example, an attribute (true, true, foo) means "this |-> foo",
  // (false, true, foo) means "~this |-> foo", and (true, false, foo) means
  // "this |-> ~foo"
  val implications = new Attribute[List[(Boolean, Boolean, Symbol)]]() // TODO: Treeify

  // If this is flop _q symbol, the corresponding _d symbol
  val flop = new Attribute[Symbol]() // TODO: Treeify

  // If this is a memory _q symbol, the corresponding we, waddr and wdata symbols
  val memory = new Attribute[(Symbol, Symbol, Symbol)]() // TODO: Treeify

  // If this is an interconnect signal, the corresponding instance symbol and port name
  val interconnect = new Attribute[Boolean]()

  // If this signal is a combinatorically driven local signal
  val combSignal = new Attribute[Boolean]()

  // The field offset if this symbol was split from a struct
  val fieldOffset = new Attribute[Int]()

  // The default value of this symbol, if required
  val default = new Attribute[Expr]() // TODO: Treeify

  // Is this an SRAM entity?
  val sram = new Attribute[Boolean]()

  // Denotes that SRAM instances should be lifted from the hierarchy below this entity
  val liftSrams = new Attribute[Boolean]()

  // Name of this symbol as declared in source, with dictionary index values
  val sourceName = new Attribute[(String, List[BigInt])]

  // Whether this choice has been generated
  val wasParam = new Attribute[Boolean]()

  // Storage slices to use for pipeline output port
  val pipelineStorage = new Attribute[List[StorageSlice]]()

  // Resolution of a dictionary symbol: 'indices' -> 'result'
  val dictResolutions = new Attribute[mutable.Map[List[BigInt], Symbol]]()

  // This choice symbol has been removed by generate processing
  val eliminated = new Attribute[Boolean]()

  // For builtin symbols, points to the implementation
  val builtin = new Attribute[BuiltinPolyFunc]()

  // Elaboration parameters for top-level entities
  val elab = new Attribute[List[Expr]]()

  // Iterator that enumerates all fields above
  private def attrIterator = Iterator(
    unused,
    topLevel,
    entry,
    stackLimit,
    recLimit,
    returnStack,
    go,
    clk,
    rst,
    payloadOfPort,
    validOfPort,
    readyOfPort,
    highLevelKind,
    clearOnStall,
    interconnectClearOnStall,
    dontCareUnless,
    implications,
    flop,
    memory,
    interconnect,
    combSignal,
    fieldOffset,
    default,
    sram,
    liftSrams,
    sourceName,
    wasParam,
    pipelineStorage,
    dictResolutions,
    eliminated,
    builtin,
    elab
  )

  // Iterator that enumerates names of fields above
  private def nameIterator = Iterator(
    "unused",
    "topLevel",
    "entry",
    "stackLimit",
    "recLimit",
    "returnStack",
    "go",
    "clk",
    "rst",
    "payloadOfPort",
    "validOfPort",
    "readyOfPort",
    "highLevelKind",
    "clearOnStall",
    "interconnectClearOnStall",
    "dontCareUnless",
    "implications",
    "flop",
    "memory",
    "interconnect",
    "combSignal",
    "fieldOffset",
    "default",
    "sram",
    "liftSrams",
    "sourceName",
    "wasParam",
    "pipelineStorage",
    "dictResolutions",
    "eliminated",
    "builtin",
    "elab"
  )

  // Copy values of attributes from another instance
  def update(that: SymbolAttributes): Unit = {
    for ((a, b) <- attrIterator zip that.attrIterator) {
      a.asInstanceOf[Attribute[Any]] update b.asInstanceOf[Attribute[Any]]
    }
  }

  // Copy values from source attributes
  def update(attr: scala.collection.Map[String, SourceAttribute])(
      implicit cc: CompilerContext): Unit =
    for ((name, sa) <- attr) {
      (name, sa) match {
        case ("unused", _: SourceAttribute.Flag)                 => unused set true
        case ("unused", _)                                       => cc.error(sa, "'unused' attribute is a flag")
        case ("stacklimit", SourceAttribute.Expr(expr))          => stackLimit set expr
        case ("stacklimit", _)                                   => cc.error(sa, "'stacklimit' attribute must be an expression")
        case ("reclimit", SourceAttribute.Expr(expr))            => recLimit set expr
        case ("reclimit", _)                                     => cc.error(sa, "'reclimit' attribute must be an expression")
        case ("toplevel", _: SourceAttribute.Flag)               => topLevel set true
        case ("toplevel", _)                                     => cc.error(sa, "'toplevel' attribute is a flag")
        case ("liftsrams", _: SourceAttribute.Flag)              => liftSrams set true
        case ("liftsrams", _)                                    => cc.error(sa, "'liftsrams' attribute is a flag")
        case ("pipelinestorage", SourceAttribute.Slices(slices)) => pipelineStorage set slices
        case ("pipelinestorage", _) =>
          cc.error(sa, "'pipelinestorage' attribute must be a list of slices")
        case _ => cc.error(sa, s"Unknown attribute '$name'")
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
