package skolemExample

type Pos = {v: BigInt with v >= 0}

sealed trait Vec[T]:
  def len: Pos = this match
    case Nil() => BigInt(0)
    case Cons(_, tail) => (1 + tail.len)

case class Nil[T]() extends Vec[T]
case class Cons[T](head: T, tail: Vec[T]) extends Vec[T]

object Vec:
  def fill[T](n: Pos, v: T): {r: Vec[T] with r.len == n} =
    if (n == 0) Nil[T]()
    else
      val r = fill(n - 1, v)
      Cons(v, r)