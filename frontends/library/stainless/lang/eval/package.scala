/* Copyright 2009-2017 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

package object eval {

  @ignore
  def force[A](expr: A): A = expr

}

