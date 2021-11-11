/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import scala.language.implicitConversions

import dotty.tools.dotc.core.Flags._
import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.Contexts._
import dotty.tools.dotc.transform.SymUtils._
import stainless.ast.SymbolIdentifier

import scala.collection.mutable.{ Map => MutableMap }

class SymbolMapping {
  /** Mapping for class invariants: class' id -> inv's id. */
  private val invs = MutableMap[SymbolIdentifier, SymbolIdentifier]()
  private val invSymbol = stainless.ast.Symbol("inv")

  /** Mapping from [[Symbol]] and the stainless identifier. */
  private val s2s = MutableMap[Symbol, SymbolIdentifier]()
  private val s2sAccessor = MutableMap[Symbol, SymbolIdentifier]()

  /** Get the identifier associated with the given [[sym]], creating a new one if needed. */
  def fetch(sym: Symbol, isAccessor: Boolean)(using Context): SymbolIdentifier = {
    if (!isAccessor) {
      s2s.getOrElseUpdate(sym, {
        val overrides = sym.allOverriddenSymbols.toSeq
        val top = overrides.lastOption.getOrElse(sym)
        if (top eq sym) {
          SymbolIdentifier(ast.Symbol(symFullName(sym)))
        } else {
          SymbolIdentifier(fetch(top, false).symbol)
        }
      })
    } else {
      s2sAccessor.getOrElseUpdate(sym, {
        val overrides = sym.allOverriddenSymbols.toSeq
        val top = overrides.lastOption.getOrElse(sym)
        if (top eq sym) {
          SymbolIdentifier(ast.Symbol(symFullName(sym)))
        } else {
          SymbolIdentifier(fetch(top, isAccessor = top.isField).symbol)
        }
      })
    }
  }

  /** Get the identifier for the class invariant of [[sym]]. */
  def fetchInvIdForClass(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = {
    val id = fetch(sym, false)
    invs.getOrElse(id, {
      val res = SymbolIdentifier(invSymbol)
      invs(id) = res
      res
    })
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