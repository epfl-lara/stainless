/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

class Symbol private[stainless](val path: Seq[String], private[stainless] val id: Int) {
  def this(name: String, id: Int) = this(name.split("\\.").toSeq, id)

  val name: String = path.mkString(".")

  override def equals(that: Any): Boolean = that match {
    case s: Symbol => id == s.id
    case _ => false
  }

  override def hashCode: Int = id

  override def toString: String = s"$name@$id"
}

object Symbol {
  private val counter = new inox.utils.UniqueCounter[Unit]

  def apply(name: String) = new Symbol(name, counter.nextGlobal)
}

class SymbolIdentifier private[stainless](id: Identifier, val symbol: Symbol)
  extends Identifier(id.name, id.globalId, id.id, alwaysShowUniqueID = false)

object SymbolIdentifier {
  def apply(name: String): SymbolIdentifier = {
    new SymbolIdentifier(FreshIdentifier(name.split("\\.").last), Symbol(name))
  }

  def apply(sym: Symbol): SymbolIdentifier = {
    new SymbolIdentifier(FreshIdentifier(sym.path.last), sym)
  }

  def unapply(id: SymbolIdentifier): Option[String] = Some(id.symbol.name)

  extension (id: Identifier) {
    def unsafeToSymbolIdentifier: SymbolIdentifier = id.asInstanceOf[SymbolIdentifier]
  }
}
