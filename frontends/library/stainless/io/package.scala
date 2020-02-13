/* Copyright 2009-2019 EPFL, Lausanne */

package stainless

import scala.language.implicitConversions

import stainless.annotation._
import stainless.lang.StaticChecks._

package object io {

  @library
  case class State(var seed: BigInt)

  @library
  def newState: State = State(0)
}

