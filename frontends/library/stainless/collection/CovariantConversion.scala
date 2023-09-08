/* Copyright 2009-2022 EPFL, Lausanne */

package stainless
package collection

import annotation._
import covcollection.{List => CovList, Nil => CovNil}

@library
object CovariantConversion {
  @library
  implicit class ToCovariantList[A](l: List[A]) {
    def toCovariantList: CovList[A] = l.foldRight(CovNil: CovList[A])(_ :: _)
  }
}