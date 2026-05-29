import language.experimental.qualifiedTypes.silent
import stainless.annotation.ignore
import scala.annotation.nowarn
import stainless.lang._

type Pos = {v: BigInt with v >= 0}

sealed trait Vec[T]:
  def len: Pos = this match
    case Nil() => BigInt(0)
    case Cons(_, tail) => (1 + tail.len)

  def zip[S](b: Vec[S] with b.len == len): {r: Vec[(T, S)] with r.len == len} =
    ((this, b) : @nowarn) match
      case (Nil(), Nil()) => Nil[(T, S)]()
      case (Cons(head, tail), Cons(bHead, bTail)) => 
        Cons((head, bHead), tail.zip(bTail))

  def concat(b: Vec[T]): {r: Vec[T] with r.len == len + b.len } =
    this match
      case Nil() => b
      case Cons(head, tail) => Cons(head, tail.concat(b))

case class Nil[T]() extends Vec[T]
case class Cons[T](head: T, tail: Vec[T]) extends Vec[T]

object Vec:
  def fill[T](n: Pos, v: T): {r: Vec[T] with r.len == n} =
    if (n == 0) Nil[T]()
    else
      val nMinus1: Pos = n - 1
      Cons(v, fill(nMinus1, v))