import stainless.lang._

object ImplicitInline {
  implicit class BD(val underlying: Boolean) {
    def f(): Unit = ()
  }

  @inline
  def inlinedFunction() = true.f()

  def caller() = inlinedFunction()
}
