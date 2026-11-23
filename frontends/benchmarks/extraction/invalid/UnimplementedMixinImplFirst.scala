import stainless.lang._

// Counterpart of verification/valid/UnimplementedMixinImplLast: `Unknown` now comes
// last in the linearization, so `Both().scale` runs its `???` body.
object UnimplementedMixinImplFirst {
  trait Scaling {
    def scale(k: BigInt): BigInt = {
      require(k >= 0)
      (??? : BigInt)
    }.ensuring(_ >= 0)
  }

  trait Unknown extends Scaling {
    override def scale(k: BigInt): BigInt = {
      require(k >= 0)
      (??? : BigInt)
    }.ensuring(_ >= 0)
  }

  trait Doubling extends Scaling {
    override def scale(k: BigInt): BigInt = {
      require(k >= 0)
      2 * k
    }.ensuring(_ >= 0)
  }

  case class Both() extends Doubling with Unknown

  def test: BigInt = {
    Both().scale(3)
  }.ensuring(_ >= 0)
}
