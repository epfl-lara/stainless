import stainless.annotation.*
import stainless.collection.*
import stainless.lang.*

object NoEq1:
  def same[T](x: T, y: T): Boolean = x == y

  def compared[@noeq T](x: T, y: T): Boolean = x == y

  def viaCall[@noeq T](x: T, y: T): Boolean = same(x, y)

  def listed[@noeq T](l: List[T]): Boolean = l.isEmpty

  def set[@noeq T](x: T): Set[T] = Set(x)

  case class Box[@noeq T](x: T)

  def boxes[@noeq T](a: Box[T], b: Box[T]): Boolean = a == b
