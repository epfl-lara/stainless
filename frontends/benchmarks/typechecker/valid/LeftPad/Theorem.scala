import stainless.annotation._
import stainless.lang._

object Theorem {
  implicit class BD(val underlying: Boolean) {

    @inline
    def proveUsing(p: Boolean): Boolean = {
      require(p && underlying)

      underlying
    } holds

    @inline
    def proved(): Boolean = {
      require(underlying)

      underlying
    } holds
  }

  @inline
  def prove(b: Boolean) = {
    require(b)

    b
  } holds
}
