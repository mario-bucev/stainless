/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import scala.language.implicitConversions
import dotty.tools.dotc.core.Flags.*
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Names.TypeName
import dotty.tools.dotc.transform.SymUtils.*
import stainless.ast.SymbolIdentifier

import scala.collection.mutable.Map as MutableMap

class SymbolMapping {
  import SymbolMapping._
  import FetchingMode._

  /** Mapping for class invariants: class' id -> inv's id. */
  private val invs = MutableMap[SymbolIdentifier, SymbolIdentifier]()
  private val invSymbol = stainless.ast.Symbol("inv")

  /** Mapping from [[Symbol]] and the stainless identifier. */
  private val s2s = MutableMap[Symbol, SymbolIdentifier]()
  private val s2sAccessor = MutableMap[Symbol, SymbolIdentifier]()
  private val s2sEnumType = MutableMap[Symbol, SymbolIdentifier]()

  /** Get the identifier associated with the given [[sym]], creating a new one if needed. */
  def fetch(sym: Symbol, mode: FetchingMode)(using dottyCtx: Context): SymbolIdentifier = mode match {
    case Plain =>
      s2s.getOrElseUpdate(sym, {
        val overrides = sym.allOverriddenSymbols.toSeq
        val top = overrides.lastOption.getOrElse(sym)
        if (top eq sym) {
          newSymbol(sym)
        } else {
          // TODO: identifier must include the sym owner, but do we need the full path? After all, the symbol is here for that...
          new SymbolIdentifier(newIdentifier(sym), fetch(top, Plain).symbol)
        }
      })
    case FieldAccessor =>
      s2sAccessor.getOrElseUpdate(sym, {
        val overrides = sym.allOverriddenSymbols.toSeq
        val top = overrides.lastOption.getOrElse(sym)
        if (top eq sym) {
          newSymbol(sym)
        } else {
          val recMode =
            if (top.isField) FieldAccessor
            else Plain
          new SymbolIdentifier(newIdentifier(sym), fetch(top, recMode).symbol)
        }
      })
    case EnumType =>
      s2sEnumType.getOrElseUpdate(sym, {
        assert(sym.allOverriddenSymbols.isEmpty)
        newSymbol(sym)
      })
  }

  /** Get the identifier for the class invariant of [[sym]]. */
  def fetchInvIdForClass(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = {
    val id = fetch(sym, Plain)
    invs.getOrElse(id, {
      val res = SymbolIdentifier(invSymbol)
      invs(id) = res
      res
    })
  }

  private def newIdentifier(sym: Symbol)(using dottyCtx: Context): Identifier =
    FreshIdentifier(
      if (sym is Param) sym.showName
      else s"${sym.owner.showFullName}.${sym.showName}")

  private def newSymbol(sym: Symbol)(using dottyCtx: Context): SymbolIdentifier = {
    val iden = newIdentifier(sym)
    val stainlessSym = {
      val suffix =
        if (sym is Method) {
          val params = sym.signature.paramsSig.collect {
            case tn: TypeName => tn.mangledString
          }
          s"(${params.mkString(",")})${sym.signature.resSig.mangledString}"
        } else ""
      ast.Symbol(
        if (sym is Param) sym.showName
        else s"${sym.showFullName}$suffix")
    }
    new SymbolIdentifier(iden, stainlessSym)
  }

  private def symFullName(sym: Symbol)(using Context): String =
    if (sym is TypeParam) {
      sym.showName
    } else {
      sym.fullName.toString.trim.split("\\.")
        .filter(_ != "package$")
        .map(name => if (name.endsWith("$")) name.init else name)
        .map(name => if (name.startsWith("_$")) name.drop(2) else name)
        .mkString(".")
    }
}

object SymbolMapping {
  enum FetchingMode {
    case Plain
    case FieldAccessor
    case EnumType
  }
}