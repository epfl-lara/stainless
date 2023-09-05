package stainless
package covcollection

import annotation._
import collection.{List => InvList, Nil => InvNil, Cons => InvCons, _}
import lang.{Option => InvOption, Some => InvSome, None => InvNone, _}

@library
object InvariantConversion {
  @library
  implicit class ToInvariantList[A](l: List[A]) {
    def toInvariantList: InvList[A] = l.foldRight(InvNil[A](): InvList[A])(_ :: _)
  }

  @library
  implicit class ToInvariantOption[A](o: Option[A]) {
    def toInvariantOption: InvOption[A] = o match {
      case None => InvNone[A]()
      case Some(x) => InvSome[A](x)
    }
  }
}