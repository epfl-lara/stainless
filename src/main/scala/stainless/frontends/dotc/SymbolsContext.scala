/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.Contexts._
import stainless.ast.SymbolIdentifier

import scala.collection.mutable.{Map => MutableMap}

class SymbolsContext {
  private val cache: MutableMap[Symbol, SymbolIdentifier] = MutableMap.empty

  def getIdentifier(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = cache.get(sym) match {
    case Some(id) => id
    case None =>
      val name = sym.name.toString
      val id = SymbolIdentifier(if (name.endsWith("$")) name.init else name)
      cache += sym -> id
      id
  }
}
