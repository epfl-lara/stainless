/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc.core.Flags._
import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.Contexts._
import stainless.ast.SymbolIdentifier

import scala.collection.mutable.{Map => MutableMap}

class SymbolsContext {
  private val symbolToSymbol: MutableMap[Symbol, ast.Symbol] = MutableMap.empty
  private val symbolToIdentifier: MutableMap[Symbol, SymbolIdentifier] = MutableMap.empty

  def getIdentifier(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = {
    symbolToIdentifier.get(sym) match {
      case Some(id) => id
      case None =>
        val overrides = sym.allOverriddenSymbols
        val top = if (overrides.nonEmpty) overrides.toSeq.last else sym
        val symbol = symbolToSymbol.get(top) match {
          case Some(symbol) => symbol
          case None =>
            val name: String = if (sym is TypeParam) {
              sym.showName
            } else {
              sym.fullName.toString.trim.split("\\.").map {
                name => if (name.endsWith("$")) name.init else name
              }.mkString(".")
            }
            val symbol = ast.Symbol(name)
            symbolToSymbol += top -> symbol
            symbol
        }

        val id = SymbolIdentifier(symbol)
        symbolToIdentifier += sym -> id
        id
    }
  }
}
