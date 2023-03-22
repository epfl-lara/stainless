object i1377 {
  sealed abstract class List[+A] {
    def :: [B >: A](elem: B): List[B] = Cons(elem, this)

    def ++[B >: A](that: List[B]): List[B] = {
      this match {
        case Nil => that
        case Cons(a, as) => a :: (as ++ that)
      }
    }

    def tail: List[A] = {
      require(this != Nil)
      this match {
        case Cons(a, as) => as
      }
    }

    def head: A = {
      require(this != Nil)
      this match {
        case Cons(a, as) => a
      }
    }
  }

  case object Nil extends List[Nothing]
  final case class Cons[+A](first: A, next: List[A]) extends List[A]

  def list: List[Int] = Cons(10, Cons(20, Cons(30, Nil)))
  def list2: List[Int] = list ++ list

  def expectedList2: List[Int] = Cons(10, Cons(20, Cons(30, Cons(10, Cons(20, Cons(30, Nil))))))
}