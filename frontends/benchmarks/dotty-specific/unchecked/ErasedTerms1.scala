
object ErasedTerms {

  def takeErased(x: BigInt)(erased y: BigInt): BigInt = {
    x + 1
  }

  def valid1(y: BigInt) = {
    erased val z: BigInt = y + 1
    takeErased(y)(z)
  } ensuring { _ > y }

  def valid2(y: BigInt) = {
    val z: BigInt = y + 1
    takeErased(y)(z)
  } ensuring { _ > y }

  def invalid1(y: BigInt) = {
    erased val z: BigInt = y + 1
    takeErased(z)(y)
  } ensuring { _ > y }

}
