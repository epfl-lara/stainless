package stainless.lang

import stainless.annotation._
import scala.language.implicitConversions

object StaticChecks {

  case class Ensuring[A](x: A) {
    @library
    def ensuring(cond: (A) => Boolean): A = x
  }

  @library
  implicit def any2Ensuring[A](x: A): Ensuring[A] = Ensuring(x)

  @library
  def require(pred: Boolean): Unit = ()

  @library
  def assert(pred: Boolean): Unit = ()

}

