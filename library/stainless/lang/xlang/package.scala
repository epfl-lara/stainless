/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

package object xlang {
  @ignore
  def epsilon[A](pred: (A) => Boolean): A = throw new RuntimeException("Implementation not supported")
}
