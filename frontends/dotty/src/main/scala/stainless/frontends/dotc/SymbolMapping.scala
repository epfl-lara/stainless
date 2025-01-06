/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import scala.language.implicitConversions

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.CompilationUnitInfo
import dotty.tools.dotc.core.Flags._
import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.Contexts._
import stainless.ast.SymbolIdentifier

import scala.collection.mutable.{ Map => MutableMap, LinkedHashMap }

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

  /** Returns a mapping from used Dotty unit trees loaded from Tasty files to their
    * [[CompilationUnitInfo]].
    *
    * Everytime a [[Symbol]] is touched through [[fetch]], we check if it has an
    * associated Tasty file. If it does, we register the symbol's root tree
    * (which is the tree of the compilation unit containing the symbol's
    * definition) and its associated compilation unit info (which contains the
    * path to the Tasty file among other things).
    *
    * We keep this information to later extract compilation units defined in
    * Tasty files, in [[StainlessExtraction.extractTastyUnits]].
    *
    * This a [[LinkedHashMap]] to keep elements in insertion order (there is no
    * efficient immutable equivalent in the Scala standard library).
    *
    * Side-effect: calling this method clears the internal list of used Tasty
    * units.
    *
    * Potential performance improvement: `Tree.equals` and `Tree.hashCode` might
    * be suboptimal. Comparing by reference sould be sufficient.
    */
  def popUsedTastyUnits(): LinkedHashMap[tpd.Tree, CompilationUnitInfo] =
    val res = usedTastyUnits
    usedTastyUnits = LinkedHashMap[tpd.Tree, CompilationUnitInfo]()
    res
  
  private var usedTastyUnits = LinkedHashMap[tpd.Tree, CompilationUnitInfo]()

  private def maybeRegisterTastyUnit(sym: Symbol)(using Context): Unit = {
    if (sym.tastyInfo.isDefined) {
      val classSym = sym.topLevelClass.asClass
      // Below, `classSym.rootTree` returns the tree read from the Tasty file.
      // It works because we passed the `-Yretain-trees` option to the compiler.
      usedTastyUnits += (classSym.rootTree -> classSym.compilationUnitInfo)
    }
  }

  /** Get the identifier associated with the given [[sym]], creating a new one if needed. */
  def fetch(sym: Symbol, mode: FetchingMode)(using Context): SymbolIdentifier = mode match {
    case Plain =>
      s2s.getOrElseUpdate(sym, {
        maybeRegisterTastyUnit(sym)
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
        maybeRegisterTastyUnit(sym)
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
        maybeRegisterTastyUnit(sym)
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
