/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import scala.language.implicitConversions

import stainless.annotation._
import stainless.lang.StaticChecks._

package object io {

  @library
  @cCode.typedef(alias = "void*", include = "")
  case class State(var seed: BigInt)

  @library
  @cCode.function(code = "static void* __FUNCTION__(void) { return NULL; }", includes = "")
  def newState: State = State(0)
}
