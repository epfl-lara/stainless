/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.io

import scala.language.implicitConversions

import stainless.annotation._
import stainless.lang.StaticChecks._

object StdOut {

  @extern
  @library
  @pure
  def print(x: Any): Unit = {
    scala.Predef.print(x)
  }

  @extern
  @library
  @pure
  def println(x: Any): Unit = {
    scala.Predef.println(x)
  }
}
