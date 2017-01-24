
object ADTInvariants1 {

  case class Positive(i: BigInt) {
    require(i > 0)
  }
  
  def theorem(f: Positive => Positive) = {
    f(Positive(1))
  } ensuring(res => res.i > 0)
}
