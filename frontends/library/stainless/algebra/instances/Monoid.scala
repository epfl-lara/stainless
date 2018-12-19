import stainless.lang._
import stainless.algebra._
import stainless.collection._
import stainless.annotation._

object Monoid {

  @induct @library
  def lemma_List_append_associativity[A](xs: List[A], ys: List[A], zs: List[A]): Boolean = {
    ((xs ++ ys) ++ zs) == (xs ++ (ys ++ zs))
  }.holds

  @library
  implicit def listMonoid[A]: Monoid[List[A]] = new Monoid[List[A]] {
    override def empty: List[A] = Nil[A]()
    override def append(xs: List[A], ys: List[A]): List[A] = xs ++ ys

    override def law_associativity(xs: List[A], ys: List[A], zs: List[A]): Boolean = {
      super.law_associativity(xs, ys, zs) because {
        lemma_List_append_associativity(xs, ys, zs)
      }
    }
  }

  //
  // @library
  // implicit def optionMonoid[A](implicit ev: Monoid[A]): Monoid[Option[A]] = new Monoid[Option[A]] {
  //   override def empty: Option[A] = None[A]()
  //   override def append(xs: Option[A], ys: Option[A]): Option[A] = (xs, ys) match {
  //     case (None(), None()) => None()
  //     case (Some(a), None()) => Some(a)
  //     case (None(), Some(a)) => Some(a)
  //     case (Some(a), Some(b)) => Some(ev.append(a, b))
  //   }

  //   override def law_associativity(xs: Option[A], ys: Option[A], zs: Option[A]): Boolean = {
  //     (xs, ys, zs) match {
  //       case (Some(x), Some(y), Some(z)) => ev.law_associativity(x, y, z)
  //       case _ => true
  //     }
  //   }
  // }
}
