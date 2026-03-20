import stainless.annotation.ignore
import scala.annotation.nowarn
import stainless.lang._

// using a type alias instead of inlining the type makes stainless sad :(
// type Pos = {v: BigInt with v >= 0}

sealed trait Vec[T]:
  def len: {v: BigInt with v >= 0} = this match
    case Nil() => (0: BigInt).ck
    case Cons(_, tail) => (1 + tail.len).ck

  def zip[S](b: Vec[S] with b.len == len): {r: Vec[(T, S)] with r.len == len} =
    ((this, b) : @nowarn) match
      case (Nil(), Nil()) => Nil[(T, S)]().ck
      case (Cons(head, tail), Cons(bHead, bTail)) => 
        Cons((head, bHead), tail.zip(bTail.ck[{b: Vec[S] with b.len == tail.len}])).ck

  def concat(b: Vec[T]): {r: Vec[T] with r.len == len + b.len } =
    this match
      case Nil() => b.ck
      case Cons(head, tail) => Cons(head, tail.concat(b)).ck

case class Nil[T]() extends Vec[T]
case class Cons[T](head: T, tail: Vec[T]) extends Vec[T]

object Vec:
  def fill[T](n: {v: BigInt with v >= 0}, v: T): {r: Vec[T] with r.len == n} =
    if (n == 0) Nil[T]().ck
    else Cons(v, fill((n - 1).ck[{v: BigInt with v >= 0}], v)).ck

extension [T](x: T)
  @ignore
  inline def ck[TT] = x.asInstanceOf[TT]