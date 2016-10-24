/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

class Symbol private(val name: String, private val id: Int) {
  override def equals(that: Any): Boolean = that match {
    case s: Symbol => id == s.id
    case _ => false
  }

  override def hashCode: Int = id
}

object Symbol {
  private val counter = new inox.utils.UniqueCounter[Unit]

  def apply(name: String) = new Symbol(name, counter.nextGlobal)
}

class SymbolIdentifier private(id: Identifier, val symbol: Symbol)
  extends Identifier(id.name, id.globalId, id.id, alwaysShowUniqueID = false)

object SymbolIdentifier {
  def apply(name: String): SymbolIdentifier = {
    new SymbolIdentifier(FreshIdentifier(name), Symbol(name))
  }

  def apply(sym: Symbol): SymbolIdentifier = {
    new SymbolIdentifier(FreshIdentifier(sym.name), sym)
  }
}
