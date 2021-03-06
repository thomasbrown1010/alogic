////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018-2019 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Factory to build output slice entities
////////////////////////////////////////////////////////////////////////////////
package com.argondesign.alogic.core

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.FlowControlTypes.FlowControlTypeNone
import com.argondesign.alogic.core.StorageTypes._
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant

import scala.collection.mutable.ListBuffer
import scala.util.ChainingSyntax

object SyncSliceFactory extends ChainingSyntax {

  /*

  // Register slice interface

  // Hardware interface:
  _ip
  _ip_valid
  _ip_ready

  _op
  _op_valid
  _op_ready

  at beginning:
  _ip_valid = 1'b0

   */

  // slice logic for void payload:
  private def voidBody(
      ss: StorageSlice,
      ipvRef: ExprSym,
      oprRef: ExprSym,
      vRef: ExprSym
  )(
      implicit cc: CompilerContext
  ): List[Stmt] = ss match {
    case StorageSliceBub =>
      // valid = ~valid & ip_valid | valid & ~op_ready;
      List(StmtAssign(vRef, ~vRef & ipvRef | vRef & ~oprRef))
    case StorageSliceFwd =>
      // valid = ip_valid | valid & ~op_ready;
      List(StmtAssign(vRef, ipvRef | vRef & ~oprRef))
    case StorageSliceBwd =>
      // valid = (valid | ip_valid) & ~op_ready;
      List(StmtAssign(vRef, (vRef | ipvRef) & ~oprRef))
  }

  // slice connects for void payload:
  private def voidConnects(
      ss: StorageSlice,
      ipvRef: ExprSym,
      iprRef: ExprSym,
      opvRef: ExprSym,
      oprRef: ExprSym,
      sRef: ExprSym,
      vRef: ExprSym
  )(
      implicit cc: CompilerContext
  ): List[EntConnect] = ss match {
    case StorageSliceBub =>
      // valid -> op_valid;
      // ~valid -> ip_ready;
      // ~valid -> space;
      List(
        EntConnect(vRef, List(opvRef)),
        EntConnect(~vRef, List(iprRef)),
        EntConnect(~vRef, List(sRef))
      )
    case StorageSliceFwd =>
      // valid -> op_valid;
      // ~valid | op_ready -> ip_ready;
      // ~valid -> space;
      List(
        EntConnect(vRef, List(opvRef)),
        EntConnect(~vRef | oprRef, List(iprRef)),
        EntConnect(~vRef, List(sRef))
      )
    case StorageSliceBwd =>
      // valid | ip_valid -> op_valid;
      // ~valid -> ip_ready;
      // ~valid -> space;
      List(
        EntConnect(vRef | ipvRef, List(opvRef)),
        EntConnect(~vRef, List(iprRef)),
        EntConnect(~vRef, List(sRef))
      )
  }

  // slice logic for non-void payload:
  private def nonVoidBody(
      ss: StorageSlice,
      ipRef: ExprSym,
      ipvRef: ExprSym,
      oprRef: ExprSym,
      pRef: ExprSym,
      vRef: ExprSym
  )(
      implicit cc: CompilerContext
  ): List[Stmt] = ss match {
    case StorageSliceBub =>
      // if (ip_valid & ~valid) {
      //   payload = ip;
      // }
      // valid = ~valid & ip_valid | valid & ~op_ready;
      List(
        StmtIf(
          ipvRef & ~vRef,
          List(StmtAssign(pRef, ipRef)),
          Nil
        ),
        StmtAssign(vRef, ~vRef & ipvRef | vRef & ~oprRef)
      )
    case StorageSliceFwd =>
      // if (ip_valid & (~valid | op_ready)) {
      //   payload = ip;
      // }
      // valid = ip_valid | valid & ~op_ready;
      List(
        StmtIf(
          ipvRef & (~vRef | oprRef),
          List(StmtAssign(pRef, ipRef)),
          Nil
        ),
        StmtAssign(vRef, ipvRef | vRef & ~oprRef)
      )
    case StorageSliceBwd =>
      // if (ip_valid & ~valid & ~op_ready) {
      //   payload = ip;
      // }
      // valid = (valid | ip_valid) & ~op_ready;
      List(
        StmtIf(
          ipvRef & ~vRef & ~oprRef,
          List(StmtAssign(pRef, ipRef)),
          Nil
        ),
        StmtAssign(vRef, (vRef | ipvRef) & ~oprRef)
      )
  }

  // slice connects for non-void payload:
  private def nonVoidConnects(
      ss: StorageSlice,
      ipRef: ExprSym,
      opRef: ExprSym,
      ipvRef: ExprSym,
      iprRef: ExprSym,
      opvRef: ExprSym,
      oprRef: ExprSym,
      sRef: ExprSym,
      pRef: ExprSym,
      vRef: ExprSym
  )(
      implicit cc: CompilerContext
  ): List[EntConnect] = ss match {
    case StorageSliceBub =>
      // payload -> op ;
      // valid -> op_valid;
      // ~valid -> ip_ready;
      // ~valid -> space;
      List(
        EntConnect(vRef, List(opvRef)),
        EntConnect(pRef, List(opRef)),
        EntConnect(~vRef, List(iprRef)),
        EntConnect(~vRef, List(sRef))
      )
    case StorageSliceFwd =>
      // payload -> op;
      // valid -> op_valid;
      // ~valid | op_ready -> ip_ready;
      // ~valid -> space;
      List(
        EntConnect(pRef, List(opRef)),
        EntConnect(vRef, List(opvRef)),
        EntConnect(~vRef | oprRef, List(iprRef)),
        EntConnect(~vRef, List(sRef))
      )
    case StorageSliceBwd =>
      // valid ? payload : ip -> op;
      // valid | ip_valid -> op_valid;
      // ~valid -> ip_ready;
      // ~valid -> space;
      List(
        EntConnect(ExprTernary(vRef, pRef, ipRef), List(opRef)),
        EntConnect(vRef | ipvRef, List(opvRef)),
        EntConnect(~vRef, List(iprRef)),
        EntConnect(~vRef, List(sRef))
      )
  }

  // Build an entity similar to the following Alogic FSM to be used as an
  // output slice implementation. The body of the main function is filled
  // in by the above implementations.
  //
  // fsm slice_bubble {
  //   // Upstream interface
  //   in payload_t ip;
  //   in bool ip_valid;
  //   out wire bool ip_ready;
  //
  //   // Downstream interface
  //   out wire payload_t op;
  //   out wire bool op_valid;
  //   in bool op_ready;
  //
  //   // Status output
  //   out wire bool space;
  //
  //   // Local storage
  //   payload_t payload;
  //   bool valid = false;
  //
  //   void main() {
  //      <BODY>
  //   }
  //
  //   <CONNECTS>
  // }
  private def buildSlice(
      ss: StorageSlice,
      name: String,
      loc: Loc,
      kind: TypeFund,
      sep: String
  )(
      implicit cc: CompilerContext
  ): (DeclEntity, DefnEntity) = {
    val fcn = FlowControlTypeNone
    val stw = StorageTypeWire

    lazy val ipSymbol = cc.newSymbol("ip", loc) tap { _.kind = TypeIn(kind, fcn) }
    val ipvSymbol = cc.newSymbol(s"ip${sep}valid", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    ipvSymbol.attr.default.set(ExprInt(false, 1, 0) regularize loc)
    val iprSymbol = cc.newSymbol(s"ip${sep}ready", loc) tap {
      _.kind = TypeOut(TypeUInt(1), fcn, stw)
    }
    iprSymbol.attr.dontCareUnless set ipvSymbol
    ipvSymbol.attr.dontCareUnless set iprSymbol
    lazy val opSymbol = cc.newSymbol("op", loc) tap { _.kind = TypeOut(kind, fcn, stw) }
    val opvSymbol = cc.newSymbol(s"op${sep}valid", loc) tap {
      _.kind = TypeOut(TypeUInt(1), fcn, stw)
    }
    val oprSymbol = cc.newSymbol(s"op${sep}ready", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    oprSymbol.attr.default.set(ExprInt(false, 1, 0) regularize loc)
    oprSymbol.attr.dontCareUnless set opvSymbol
    opvSymbol.attr.dontCareUnless set oprSymbol
    val sSymbol = cc.newSymbol("space", loc) tap { _.kind = TypeOut(TypeUInt(1), fcn, stw) }
    lazy val pSymbol = cc.newSymbol("payload", loc) tap { _.kind = kind }
    val vSymbol = cc.newSymbol("valid", loc) tap { _.kind = TypeUInt(1) }

    lazy val ipDecl = ipSymbol.mkDecl regularize loc
    val ipvDecl = ipvSymbol.mkDecl regularize loc
    val iprDecl = iprSymbol.mkDecl regularize loc
    lazy val opDecl = opSymbol.mkDecl regularize loc
    val opvDecl = opvSymbol.mkDecl regularize loc
    val oprDecl = oprSymbol.mkDecl regularize loc
    val sDecl = sSymbol.mkDecl regularize loc
    lazy val pDecl = pSymbol.mkDecl regularize loc
    val vDecl = vSymbol.mkDecl regularize loc

    lazy val ipDefn = ipSymbol.mkDefn
    val ipvDefn = ipvSymbol.mkDefn
    val iprDefn = iprSymbol.mkDefn
    lazy val opDefn = opSymbol.mkDefn
    val opvDefn = opvSymbol.mkDefn
    val oprDefn = oprSymbol.mkDefn
    val sDefn = sSymbol.mkDefn
    lazy val pDefn = pSymbol.mkDefn
    val vDefn = vSymbol.mkDefn(ExprInt(false, 1, 0))

    lazy val ipRef = ExprSym(ipSymbol)
    val ipvRef = ExprSym(ipvSymbol)
    val iprRef = ExprSym(iprSymbol)
    lazy val opRef = ExprSym(opSymbol)
    val opvRef = ExprSym(opvSymbol)
    val oprRef = ExprSym(oprSymbol)
    val sRef = ExprSym(sSymbol)
    lazy val pRef = ExprSym(pSymbol)
    val vRef = ExprSym(vSymbol)

    val statements = if (kind != TypeVoid) {
      nonVoidBody(ss, ipRef, ipvRef, oprRef, pRef, vRef)
    } else {
      voidBody(ss, ipvRef, oprRef, vRef)
    }

    val decls = {
      if (kind != TypeVoid) {
        List(ipDecl, ipvDecl, iprDecl, opDecl, opvDecl, oprDecl, sDecl, pDecl, vDecl)
      } else {
        List(ipvDecl, iprDecl, opvDecl, oprDecl, sDecl, vDecl)
      }
    }

    val defns = {
      if (kind != TypeVoid) {
        List(ipDefn, ipvDefn, iprDefn, opDefn, opvDefn, oprDefn, sDefn, pDefn, vDefn)
      } else {
        List(ipvDefn, iprDefn, opvDefn, oprDefn, sDefn, vDefn)
      }
    } map {
      EntDefn
    }

    val connects = if (kind != TypeVoid) {
      nonVoidConnects(ss, ipRef, opRef, ipvRef, iprRef, opvRef, oprRef, sRef, pRef, vRef)
    } else {
      voidConnects(ss, ipvRef, iprRef, opvRef, oprRef, sRef, vRef)
    }

    val entitySymbol = cc.newSymbol(name, loc)
    val decl = DeclEntity(entitySymbol, decls) regularize loc
    val defn = DefnEntity(
      entitySymbol,
      EntityVariant.Fsm,
      defns ::: EntCombProcess(statements) :: connects
    ) regularize loc
    (decl, defn)
  }

  // Given a list of slice instances, build an entity that
  // instantiates each and connects them back to back
  private def buildCompoundSlice(
      slices: List[(DeclEntity, DefnEntity)],
      name: String,
      loc: Loc,
      kind: TypeFund,
      sep: String
  )(
      implicit cc: CompilerContext
  ): (DeclEntity, DefnEntity) = {
    val nSlices = slices.length
    require(nSlices >= 2)

    val fcn = FlowControlTypeNone
    val stw = StorageTypeWire

    val ipName = "ip"
    val ipvName = s"$ipName${sep}valid"
    val iprName = s"$ipName${sep}ready"

    val opName = "op"
    val opvName = s"$opName${sep}valid"
    val oprName = s"$opName${sep}ready"

    lazy val ipSymbol = cc.newSymbol(ipName, loc) tap { _.kind = TypeIn(kind, fcn) }
    val ipvSymbol = cc.newSymbol(ipvName, loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    ipvSymbol.attr.default.set(ExprInt(false, 1, 0) regularize loc)
    val iprSymbol = cc.newSymbol(iprName, loc) tap { _.kind = TypeOut(TypeUInt(1), fcn, stw) }
    iprSymbol.attr.dontCareUnless set ipvSymbol
    ipvSymbol.attr.dontCareUnless set iprSymbol
    lazy val opSymbol = cc.newSymbol(opName, loc) tap { _.kind = TypeOut(kind, fcn, stw) }
    val opvSymbol = cc.newSymbol(opvName, loc) tap { _.kind = TypeOut(TypeUInt(1), fcn, stw) }
    val oprSymbol = cc.newSymbol(oprName, loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    oprSymbol.attr.default.set(ExprInt(false, 1, 0) regularize loc)
    oprSymbol.attr.dontCareUnless set opvSymbol
    opvSymbol.attr.dontCareUnless set oprSymbol
    val sSymbol = cc.newSymbol("space", loc) tap { _.kind = TypeOut(TypeUInt(nSlices), fcn, stw) }

    lazy val ipDecl = ipSymbol.mkDecl regularize loc
    val ipvDecl = ipvSymbol.mkDecl regularize loc
    val iprDecl = iprSymbol.mkDecl regularize loc
    lazy val opDecl = opSymbol.mkDecl regularize loc
    val opvDecl = opvSymbol.mkDecl regularize loc
    val oprDecl = oprSymbol.mkDecl regularize loc
    val sDecl = sSymbol.mkDecl regularize loc

    lazy val ipDefn = ipSymbol.mkDefn
    val ipvDefn = ipvSymbol.mkDefn
    val iprDefn = iprSymbol.mkDefn
    lazy val opDefn = opSymbol.mkDefn
    val opvDefn = opvSymbol.mkDefn
    val oprDefn = oprSymbol.mkDefn
    val sDefn = sSymbol.mkDefn

    lazy val ipRef = ExprSym(ipSymbol)
    val ipvRef = ExprSym(ipvSymbol)
    val iprRef = ExprSym(iprSymbol)
    lazy val opRef = ExprSym(opSymbol)
    val opvRef = ExprSym(opvSymbol)
    val oprRef = ExprSym(oprSymbol)
    val sRef = ExprSym(sSymbol)

    val iSymbols = slices.zipWithIndex map {
      case ((decl, _), index) =>
        val eSymbol = decl.symbol
        val iSymbol = cc.newSymbol(s"slice_$index", loc)
        iSymbol.kind = eSymbol.kind.asType.kind
        iSymbol
    }

    val iDecls = iSymbols map { _.mkDecl regularize loc }

    val iDefns = iSymbols map { _.mkDefn }

    val iRefs = iSymbols map ExprSym

    val connects = new ListBuffer[EntConnect]()

    // Create the cascade connection
    if (kind != TypeVoid) {
      // Payload
      connects append EntConnect(ipRef, List(iRefs.head select ipName))
      for ((aRef, bRef) <- iRefs zip iRefs.tail) {
        connects append EntConnect(aRef select opName, List(bRef select ipName))
      }
      connects append EntConnect(iRefs.last select opName, List(opRef))
    }

    // Valid
    connects append EntConnect(ipvRef, List(iRefs.head select ipvName))
    for ((aRef, bRef) <- iRefs zip iRefs.tail) {
      connects append EntConnect(aRef select opvName, List(bRef select ipvName))
    }
    connects append EntConnect(iRefs.last select opvName, List(opvRef))

    // Ready
    connects append EntConnect(oprRef, List(iRefs.last select oprName))
    for ((aRef, bRef) <- (iRefs zip iRefs.tail).reverse) {
      connects append EntConnect(bRef select iprName, List(aRef select oprName))
    }
    connects append EntConnect(iRefs.head select iprName, List(iprRef))

    // Build the space, empty and full signals
    connects append EntConnect(ExprCat(iRefs.reverse map { _ select "space" }), List(sRef))

    // Put it all together
    val decls = {
      if (kind != TypeVoid) {
        List(ipDecl, ipvDecl, iprDecl, opDecl, opvDecl, oprDecl, sDecl) ::: iDecls
      } else {
        List(ipvDecl, iprDecl, opvDecl, oprDecl, sDecl) ::: iDecls
      }
    }

    val defns = {
      if (kind != TypeVoid) {
        List(ipDefn, ipvDefn, iprDefn, opDefn, opvDefn, oprDefn, sDefn) ::: iDefns
      } else {
        List(ipvDefn, iprDefn, opvDefn, oprDefn, sDefn) ::: iDefns
      }
    } map {
      EntDefn
    }

    val entitySymbol = cc.newSymbol(name, loc)
    val decl = DeclEntity(entitySymbol, decls) regularize loc
    val defn = DefnEntity(
      entitySymbol,
      EntityVariant.Net,
      defns ::: connects.toList
    ) regularize loc
    (decl, defn)
  }

  def apply(
      slices: List[StorageSlice],
      prefix: String,
      loc: Loc,
      kind: TypeFund
  )(
      implicit cc: CompilerContext
  ): List[(DeclEntity, DefnEntity)] = {
    require(slices.nonEmpty)
    require(kind.isPacked)

    lazy val fslice = buildSlice(StorageSliceFwd, s"$prefix${cc.sep}fslice", loc, kind, cc.sep)
    lazy val bslice = buildSlice(StorageSliceBwd, s"$prefix${cc.sep}bslice", loc, kind, cc.sep)
    lazy val bubble = buildSlice(StorageSliceBub, s"$prefix${cc.sep}bubble", loc, kind, cc.sep)

    val sliceEntities = slices map {
      case StorageSliceFwd => fslice
      case StorageSliceBwd => bslice
      case StorageSliceBub => bubble
    }

    if (sliceEntities.lengthIs == 1) {
      // If just one, we are done
      sliceEntities
    } else {
      // Otherwise build the compound entity
      val compoundName = s"$prefix${cc.sep}slices"
      val compoundEntity = buildCompoundSlice(sliceEntities, compoundName, loc, kind, cc.sep)
      // The compound entity must be first, and add the distinct slices
      compoundEntity :: sliceEntities.distinct
    }
  }

}
