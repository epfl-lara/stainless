import stainless.lang._
import stainless.collection._

object Zip {
  def zip[A, B](a: List[A], b: List[B] with b.size == a.size): {l: List[(A, B)] with l.size == a.size} = {
    (a, b) match {
      case (Nil(), Nil()) => Nil[(A, B)]().asInstanceOf[{l: List[(A, B)] with l.size == a.size}]
      case (Cons(h1, t1), Cons(h2, t2)) => 
        Cons(
          (h1, h2),
          zip(t1, t2.asInstanceOf[{ b: List[B] with b.size == t1.size}])
        ).asInstanceOf[{l: List[(A, B)] with l.size == a.size}]
    }
  }
}