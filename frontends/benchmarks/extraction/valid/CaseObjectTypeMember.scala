import stainless.lang._

trait One {
  type T
  def f(): Option[T]
}

case object OneImpl extends One {
  type T = BigInt
  def f(): Option[T] = None()
}
