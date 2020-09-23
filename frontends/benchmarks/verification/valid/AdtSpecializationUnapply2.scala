import stainless.lang.Option

object AdtSpecializationUnapply2 {
  sealed trait Root
  sealed trait B extends Root { val x: BigInt }
  case class C(x: BigInt) extends B
  case class D(x: BigInt) extends B

  def keepIsEmpty(o: Option[BigInt]) =
    o.isEmpty

  def f(a: Root): BigInt =
    a match {
      // Will be translated to an unapply that essentially checks `b is C || b is D`
      case b: B => b.x
      case _ => 0
    }
}
