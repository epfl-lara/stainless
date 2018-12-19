package stainless
package algebra
package instances

import stainless.lang._
import stainless.annotation._

object Order {

  // @library
  // implicit val bigIntOrder: Order[BigInt] = new Order[BigInt] {
  //   override def eqv(x: BigInt, y: BigInt): Boolean = {
  //     x == y
  //   }

  //   override def lteqv(x: BigInt, y: BigInt): Boolean = {
  //     x <= y
  //   }

  //   override def compare(x: BigInt, y: BigInt): Int = {
  //     if (x < y) -1 else if (x == y) 0 else 1
  //   }

  //   override def partialCompare(x: BigInt, y: BigInt): Comparison = {
  //     import Comparison._
  //     if (x < y) Less else if (x == y) Equals else Greater
  //   }
  // }

  // @library
  // implicit val intOrder: Order[Int] = new Order[Int] {
  //   override def eqv(x: Int, y: Int): Boolean = {
  //     x == y
  //   }

  //   override def lteqv(x: Int, y: Int): Boolean = {
  //     x <= y
  //   }

  //   override def compare(x: Int, y: Int): Int = {
  //     if (x < y) -1 else if (x == y) 0 else 1
  //   }

  //   override def partialCompare(x: Int, y: Int): Comparison = {
  //     import Comparison._
  //     if (x < y) Less else if (x == y) Equals else Greater
  //   }
  // }

  // @library
  // implicit val booleanOrder: Order[Boolean] = new Order[Boolean] {
  //   override def eqv(x: Boolean, y: Boolean): Boolean = {
  //     x == y
  //   }

  //   override def lteqv(x: Boolean, y: Boolean): Boolean = {
  //     if (!x && y) true else if (x == y) true else false
  //   }

  //   override def compare(x: Boolean, y: Boolean): Int = {
  //     if (!x && y) -1 else if (x == y) 0 else 1
  //   }

  //   override def partialCompare(x: Boolean, y: Boolean): Comparison = {
  //     import Comparison._
  //     if (!x && y) Less else if (x == y) Equals else Greater
  //   }
  // }

  // @library
  // implicit def optionOrder[A](implicit ev: Order[A]): Order[Option[A]] = {
  //   new Order[Option[A]] {
  //     override def eqv(x: Option[A], y: Option[A]): Boolean = {
  //       (x, y) match {
  //         case (None(), None())   => true
  //         case (Some(x), Some(y)) => ev.eqv(x, y)
  //         case _                  => false
  //       }
  //     }

  //     override def lteqv(x: Option[A], y: Option[A]): Boolean = {
  //       (x, y) match {
  //         case (None(), _)        => true
  //         case (Some(x), Some(y)) => ev.lteqv(x, y)
  //         case _                  => false
  //       }
  //     }

  //     override def compare(x: Option[A], y: Option[A]): Int = {
  //       (x, y) match {
  //         case (None(), _)        => -1
  //         case (Some(x), Some(y)) => ev.compare(x, y)
  //         case _                  => 1
  //       }
  //     }

  //     override def partialCompare(x: Option[A], y: Option[A]): Comparison = {
  //       import Comparison._
  //       if (compare(x, y) < 0) Less
  //       else if (compare(x, y) == 0) Equals
  //       else Greater
  //     }

  //     override def law_reflexivity(x: Option[A]) = {
  //       x match {
  //         case Some(a) => ev.law_reflexivity(a)
  //         case None() => true
  //       }
  //     }

  //     override def law_antiSymmetry(x: Option[A], y: Option[A]) = {
  //       (x, y) match {
  //         case (Some(a), Some(b)) => ev.law_antiSymmetry(a, b)
  //         case _ => true
  //       }
  //     }

  //     override def law_transitivity(x: Option[A], y: Option[A], z: Option[A]) = {
  //       (x, y, z) match {
  //         case (Some(a), Some(b), Some(c)) => ev.law_transitivity(a, b, c)
  //         case _ => true
  //       }
  //     }

  //     override def law_totality(x: Option[A], y: Option[A]): Boolean = {
  //       (x, y) match {
  //         case (Some(a), Some(b)) => ev.law_totality(a, b)
  //         case _ => true
  //       }
  //     }
  //   }
  // }
}
