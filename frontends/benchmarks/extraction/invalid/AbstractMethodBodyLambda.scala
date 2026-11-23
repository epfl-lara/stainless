import stainless.lang._

// First-class functions cannot be overridden.
object AbstractMethodBodyLambda {
  def pick: BigInt => BigInt = (x: BigInt) => AbstractMethodBody[BigInt]()
}
