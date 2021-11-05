/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import scala.language.implicitConversions

import dotty.tools.dotc.core.Flags._
import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.Contexts._
import stainless.ast.SymbolIdentifier

import scala.collection.mutable.{ Map => MutableMap }

class SymbolsContext {
  /*
  /** Get the identifier associated with the given [[sym]], creating a new one if needed. */
  def fetch(sym: Symbol)(using Context): SymbolIdentifier = synchronized {
    val path = getPath(sym)
    s2i.getOrElseUpdate(path, {
      val overrides = sym.allOverriddenSymbols.toSeq
      val top = overrides.lastOption.getOrElse(sym)
      val symbol = s2s.getOrElseUpdate(top, ast.Symbol(symFullName(sym)))
      SymbolIdentifier(symbol)
    })
  }
  */
/*
  /** Mapping from [[Symbol]] (or rather: its path) and the stainless identifier. */
  private val s2i = MutableMap[String, SymbolIdentifier]()

  /** Mapping useful to use the same top symbol mapping. */
  private val s2s = MutableMap[Symbol, ast.Symbol]()
*/
  /** Mapping for class invariants: class' id -> inv's id. */
  private val invs = MutableMap[SymbolIdentifier, SymbolIdentifier]()
  private val invSymbol = stainless.ast.Symbol("inv")
  /*
  /** Mapping for getter identifiers. */
  //  private val params = MutableMap[ast.Symbol, SymbolIdentifier]()
  private val params = MutableMap[SymbolIdentifier, SymbolIdentifier]()
  */

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

  private val s2s = MutableMap[Symbol, SymbolIdentifier]()
  private val s2sAccessor = MutableMap[Symbol, SymbolIdentifier]()

  import dotty.tools.dotc.transform.SymUtils._

  def fetch(sym: Symbol, isAccessor: Boolean)(using Context): SymbolIdentifier = synchronized {
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
          /*
          s2s.getOrElse(top, {
            SymbolIdentifier(fetch(top, true).symbol) // TODO: Comment peut-on savoir si sym est un accessor ou pas????
          })
          */
        }
      })
    }
//    s2s.getOrElseUpdate(sym, {
//      val overrides = sym.allOverriddenSymbols.toSeq
//      val top = overrides.lastOption.getOrElse(sym)
//    })
  }


/*
  private val fieldAccessor2sym = MutableMap[String, SymbolIdentifier]()
  private val fieldAccessorSym2sym = MutableMap[Symbol, ast.Symbol]()
*/
/*
  def fetchFieldAccessor(sym: Symbol)(using Context): SymbolIdentifier = synchronized {
    val path = getPath(sym)
    fieldAccessor2sym.getOrElseUpdate(path, {
      val overrides = sym.allOverriddenSymbols.toSeq
      val top = overrides.lastOption.getOrElse(sym)
      // si top == sym, comme d'hab. Sinon, on doit choper le field accessor qui est overriden?
      if (top eq sym) {
        val symbol = fieldAccessorSym2sym.getOrElseUpdate(top, ast.Symbol(symFullName(sym)))
        SymbolIdentifier(symbol)
      } else {

//        SymbolIdentifier(fetchFieldAccessor(top).symbol)
      }
    })
  }
*/

/*
  def fetchParam(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = synchronized {
    /*
    val id = fetch(sym)
    params.getOrElse(id, {
      // not freshening: "key not found: z" dans MethodLifting (GoodInitialization) parce que val x et def x ont le meme symbol
      val res = SymbolIdentifier(id.symbol)
      params(id) = res
      res
    })
    */
    /*
    val id = fetch(sym)
    // id.symbol: SoundInvariant fails because the overriden x gets the same SymbolIdentifier (it should not)
    params.getOrElse(id.symbol, {
      val res = id.freshen
      params(id.symbol) = res
      res
    })
    */
    val id = fetch(sym, false)
    params.getOrElse(id, {
//      val res = id.freshen
      val res = SymbolIdentifier(id.symbol)
      params(id) = res
      res
    })
  }
*/
  /** Get the identifier for the class invariant of [[sym]]. */
  def fetchInvIdForClass(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = synchronized {
    val id = fetch(sym, false)
    invs.getOrElse(id, {
      val res = SymbolIdentifier(invSymbol)
      invs(id) = res
      res
    })
  }

  private def getPath(sym: Symbol)(implicit ctx: Context): String = {
    sym.fullName.toString.trim.split("\\.").mkString(".") + sym.id.toString
  }

}


