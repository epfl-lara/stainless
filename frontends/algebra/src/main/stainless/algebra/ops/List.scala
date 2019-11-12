package stainless
package algebra
package ops

import stainless.lang._
import stainless.annotation._
import stainless.collection.{List => StainlessList}

object List {

  @library
  implicit class ListOps[A](val list: StainlessList[A]) extends AnyVal {
    @library
    final def foldMap[B](f: A => B)(implicit M: Monoid[B]): B = {
      list.map(f).foldLeft(M.identity)(M.combine)
    }
  }
}

