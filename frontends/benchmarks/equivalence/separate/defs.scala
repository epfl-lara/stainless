import stainless.lang._

object defs {
  sealed trait Animal
  case class Sheep(id: BigInt) extends Animal
  case class Goat(id: BigInt) extends Animal

  sealed abstract class List[+T] {
    def size: Int = {
      this match {
        case Nil => 0
        case h :: t =>
          val tLen = t.size
          if (tLen == Int.MaxValue) tLen
          else 1 + tLen
      }
   }.ensuring(res => 0 <= res && res <= Int.MaxValue)

    def length: Int = size

    def ++[TT >: T](that: List[TT]): List[TT] = {
      this match {
        case Nil => that
        case x :: xs => x :: (xs ++ that)
      }
    }

    def head: T = {
      require(this != Nil)
      val h :: _ = this: @unchecked
      h
    }

    def tail: List[T] = {
      require(this != Nil)
      val _ :: t = this: @unchecked
      t
    }

    def apply(index: Int): T = {
      require(0 <= index && index < size)
      decreases(index)
      if (index == 0) {
        head
      } else {
        tail(index-1)
      }
    }

    def :: [TT >: T](elem: TT): List[TT] = new ::(elem, this)

    def :+[TT >: T](t: TT): List[TT] = {
      this match {
        case Nil => t :: this
        case x :: xs => x :: (xs :+ t)
      }
    }
  }

  case object Nil extends List[Nothing]

  final case class ::[+A](first: A, next: List[A]) extends List[A]

}
