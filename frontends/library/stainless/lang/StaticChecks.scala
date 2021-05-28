package stainless.lang

import stainless.annotation._

object StaticChecks {

  @library
  implicit class Ensuring[A](val x: A) extends AnyVal {
    def ensuring(@ghost cond: (A) => Boolean): A = x
  }

  @library @ignore
  implicit class WhileDecorations(val u: Unit) {
    def invariant(@ghost x: Boolean): Unit = {
      require(x)
      u
    }

    def weakInvariant(@ghost x: Boolean): Unit = {
      require(x)
      u
    }

    def inline: Unit = { }
    def opaque: Unit = { }
  }

  @library
  def require(@ghost pred: Boolean): Unit = ()

  @library
  def assert(@ghost pred: Boolean): Unit = ()

}

