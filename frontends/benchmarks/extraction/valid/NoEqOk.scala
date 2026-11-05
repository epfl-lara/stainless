import stainless.annotation.*
import stainless.lang.*

object NoEqOk:
  // A `@noeq` type parameter can be instantiated with `Any` (which also counts as mutable)
  def first[@noeq @mutable T](x: T, y: T): T = x

  def any(): Boolean = first[Any](1, 2L).isInstanceOf[Int]

  def pair[@noeq @mutable T](x: T, y: T): (T, T) = (x, y)

  def anyPair(): Boolean = pair[Any](1, 2L)._1.isInstanceOf[Int]

  // A `@noeq` type parameter can be passed for another one
  def viaCall[@noeq @mutable T](x: T, y: T): T = first(x, y)

  // A `@noeq` type member can be defined as `Any`
  sealed abstract class Container:
    @noeq type Elem
    def elem: Elem

  case class AnyContainer(elem: Any) extends Container:
    type Elem = Any

  // An equality type parameter can be instantiated with any type that does not reach `Any`
  def same[T](x: T, y: T): Boolean = x == y

  def ok(): Boolean = same[(BigInt, Option[Int])]((1, None()), (1, None()))

  // An overriding method may annotate a type parameter that the overridden one does not
  abstract class Base:
    def id[T](x: T): T

  case class Impl() extends Base:
    def id[@noeq T](x: T): T = x

  // A subclass may be stricter than its parent: no `Child[Any]` can be built, so no `Parent[Any]` is a `Child`
  sealed abstract class Parent[@noeq @mutable T]

  case class Child[T](x: T) extends Parent[T]:
    def same(y: T): Boolean = x == y
