import stainless.lang._

// With mixins, the method that runs is the last one in the linearization.
// Here `Doubling` comes after `Unknown`, so the implementation wins over `???`.
object UnimplementedMixinImplLast {
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

  case class Both() extends Unknown with Doubling

  def test: BigInt = {
    Both().scale(3)
  }.ensuring(_ >= 0)
}
