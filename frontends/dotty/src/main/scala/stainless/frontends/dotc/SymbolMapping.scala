/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import scala.language.implicitConversions

import dotty.tools.dotc.core.Flags._
import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.Contexts._
import stainless.ast.SymbolIdentifier

import scala.collection.mutable.{ Map => MutableMap }

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
  def fetch(sym: Symbol, mode: FetchingMode)(using Context): SymbolIdentifier = mode match {
    case Plain =>
      s2s.getOrElseUpdate(sym, {
        val overrides = sym.allOverriddenSymbols.toSeq
        val top = overrides.lastOption.getOrElse(sym)
        if (top eq sym) {
          SymbolIdentifier(ast.Symbol(symFullName(sym)))
        } else {
          SymbolIdentifier(fetch(top, Plain).symbol)
        }
      })
    case FieldAccessor =>
      s2sAccessor.getOrElseUpdate(sym, {
        val overrides = sym.allOverriddenSymbols.toSeq
        val top = overrides.lastOption.getOrElse(sym)
        if (top eq sym) {
          SymbolIdentifier(ast.Symbol(symFullName(sym)))
        } else {
          val recMode =
            if (top.isField) FieldAccessor
            else Plain
          SymbolIdentifier(fetch(top, recMode).symbol)
        }
      })
    case EnumType =>
      s2sEnumType.getOrElseUpdate(sym, {
        assert(sym.allOverriddenSymbols.isEmpty)
        SymbolIdentifier(ast.Symbol(symFullName(sym)))
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
}

object SymbolMapping {

  enum FetchingMode {
    case Plain
    case FieldAccessor
    case EnumType
  }

  private def symFullName(sym: Symbol)(using Context): String =
    if (sym `is` TypeParam) {
      sym.showName
    } else {
      sym.fullName.toString.trim.split("\\.")
        .filter(_ != "package$")
        .map(name => if (name.endsWith("$")) name.init else name)
        .map { name =>
          // Strip the _$ introduced for each scope of inner function
          var nme = name
          while (nme.startsWith("_$")) {
            nme = nme.drop(2)
          }
          nme
        }
        .mkString(".")
    }
}