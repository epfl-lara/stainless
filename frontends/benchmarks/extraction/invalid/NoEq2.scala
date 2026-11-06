import stainless.annotation.*

object NoEq2:
  abstract class Base:
    def same[@noeq T](x: T, y: T): Boolean

  case class Impl() extends Base:
    def same[T](x: T, y: T): Boolean = x == y

  abstract class Container:
    @noeq type Elem
    def elem: Elem
    def contains(x: Elem): Boolean = elem == x
