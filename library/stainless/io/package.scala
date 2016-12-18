/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

package object io {

  import stainless.annotation._

  @library
  case class State(var seed: BigInt)

  @library
  def newState: State = State(0)
}

