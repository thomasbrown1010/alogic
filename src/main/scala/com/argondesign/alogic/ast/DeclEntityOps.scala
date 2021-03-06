////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2019 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.ast

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.Symbols.Symbol

trait DeclEntityOps { this: DeclEntity =>

  final lazy val entities: List[DeclEntity] = decls collect {
    case decl: DeclEntity => decl
  }

  final lazy val instances: List[DeclInstance] = decls collect {
    case decl: DeclInstance => decl
  }

  final lazy val functions: List[DeclFunc] = decls collect {
    case decl: DeclFunc => decl
  }

  final lazy val states: List[DeclState] = decls collect {
    case decl: DeclState => decl
  }

  final lazy val ports: List[Symbol] = decls collect {
    case decl: DeclIn  => decl.symbol
    case decl: DeclOut => decl.symbol
  }

  final lazy val clk: Option[Symbol] =
    decls collectFirst { case Decl(symbol) if symbol.attr.clk.isSet => symbol }

  final lazy val rst: Option[Symbol] =
    decls collectFirst { case Decl(symbol) if symbol.attr.rst.isSet => symbol }

  final lazy val go: Option[Symbol] =
    decls collectFirst { case Decl(symbol) if symbol.attr.go.isSet => symbol }
}
