package stainless.lang

import stainless.annotation._
import scala.language.implicitConversions

object StaticChecks {

  @library
  case class Ensuring[A](x: A) {
    def ensuring(@ghost cond: (A) => Boolean): A = x
  }

  @library
  implicit def any2Ensuring[A](x: A): Ensuring[A] = Ensuring(x)

  @library
  def require(@ghost pred: Boolean): Unit = ()

  @library
  def assert(@ghost pred: Boolean): Unit = ()

}

