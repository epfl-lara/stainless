/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontends.dotc

import scala.language.implicitConversions

import dotty.tools.dotc.core.Flags._
import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.Contexts._
import stainless.ast.SymbolIdentifier

import scala.collection.mutable.{ Map => MutableMap }

class SymbolsContext {

  /** Get the identifier associated with the given [[sym]], creating a new one if needed. */
  def fetch(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = synchronized {
    val path = getPath(sym)
    s2i.getOrElse(path, {
      val overrides = sym.allOverriddenSymbols
      val top = if (overrides.nonEmpty) overrides.toSeq.last else sym
      val symbol = s2s.getOrElse(top, {
        val name: String =
          if (sym is TypeParam) {
            sym.showName
          } else {
            sym.fullName.toString.trim.split("\\.")
              .filter(_ != "package$")
              .map(name => if (name.endsWith("$")) name.init else name)
              .map(name => if (name.startsWith("_$")) name.drop(2) else name)
              .mkString(".")
          }

        val res = ast.Symbol(name)
        s2s(top) = res
        res
      })

      val res = SymbolIdentifier(symbol)
      s2i(path) = res
      res
    })
  }

  def fetchParam(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = synchronized {
    val id = fetch(sym)
    params.getOrElse(id, {
      val res = SymbolIdentifier(id.symbol)
      params(id) = res
      res
    })
  }

  /** Get the identifier for the class invariant of [[sym]]. */
  def fetchInvIdForClass(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = synchronized {
    val id = fetch(sym)
    invs.getOrElse(id, {
      val res = SymbolIdentifier(invSymbol)
      invs(id) = res
      res
    })
  }

  private def getPath(sym: Symbol)(implicit ctx: Context): String = sym.fullName + sym.id.toString

  /** Mapping from [[Symbol]] (or rather: its path) and the stainless identifier. */
  private val s2i = MutableMap[String, SymbolIdentifier]()

  /** Mapping useful to use the same top symbol mapping. */
  private val s2s = MutableMap[Symbol, ast.Symbol]()

  /** Mapping for class invariants: class' id -> inv's id. */
  private val invs = MutableMap[SymbolIdentifier, SymbolIdentifier]()
  private val invSymbol = stainless.ast.Symbol("inv")

  /** Mapping for getter identifiers. */
  private val params = MutableMap[SymbolIdentifier, SymbolIdentifier]()
}


