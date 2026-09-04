// see https://github.com/epfl-lara/stainless/issues/1670
object ErasedParameters:
  case class C(erased x: Int):
    def cp: C = {
      erased val x1: Int = 3
      C(x1)
    }
