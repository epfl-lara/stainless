package stainless.algebra
package ops

import stainless.lang._
import stainless.collection.{List => StainlessList}

object List {

  implicit class ListOps[A](val list: StainlessList[A]) extends AnyVal {
    final def foldMap[B](f: A => B)(implicit M: Monoid[B]): B = {
      list.map(f).foldLeft(M.identity)(M.combine)
    }
  }
}

