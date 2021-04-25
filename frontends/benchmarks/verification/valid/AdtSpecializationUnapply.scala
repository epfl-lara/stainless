object AdtSpecializationUnapply {
  sealed trait A
  sealed trait B extends A { val x: BigInt }
  case class C(x: BigInt) extends B
  case class D(x: BigInt) extends B
  case class E(b: Boolean) extends A

  def f(a: A): BigInt = a match {
    // Will be translated to an unapply that essentially checks `b is C || b is D`
    case b: B => b.x
    case _ => 0
  }
}
