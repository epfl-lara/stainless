/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import stainless.annotation._

package object io {

  @library
  @cCode.typedef(alias = "void*", include = "")
  case class State(var seed: BigInt)

  @library
  @cCode.function(
    code =
      """|void* __FUNCTION__(void) {
         |  return NULL;
         |}""",
    headerIncludes = "",
    cIncludes = ""
  )
  def newState: State = State(0)
}
