import stainless.annotation.ignore
import scala.annotation.nowarn
import stainless.lang._

sealed trait Vec[T]:
  def len: { r: BigInt with r >= 0 } = this match
    case Nil() => (0: BigInt).ck
    case Cons(_, tail) => (1 + tail.len).ck

  def zip[S](b: Vec[S] with b.len == len): {r: Vec[(T, S)] with r.len == len} =
    ((this, b) : @nowarn) match
      case (Nil(), Nil()) => Nil[(T, S)]().ck
      case (Cons(head, tail), Cons(bHead, bTail)) => 
        Cons((head, bHead), tail.zip(bTail.ck)).ck

  def concat(b: Vec[T]): {r: Vec[T] with r.len == len + b.len } =
    this match
      case Nil() => b.ck
      case Cons(head, tail) => Cons(head, tail.concat(b)).ck

case class Nil[T]() extends Vec[T]
case class Cons[T](head: T, tail: Vec[T]) extends Vec[T]

object Vec:
  def fill[T](n: BigInt with n >= 0, v: T): {r: Vec[T] with r.len == n} =
    if (n == 0) Nil[T]().ck
    else Cons(v, fill((n - 1).ck, v)).ck

extension [T](x: T)
  @ignore
  inline def ck[TT] = x.asInstanceOf[TT]