object Test {
  abstract class OOPS { // OOP Stupid
    def test(x: BigInt) = x
    def check: Unit = {
      assert(test(3) == 3)
    }
  }
  case class OOPSI() extends OOPS { // OOP Stupid Indeed
    override def test(x: BigInt): BigInt = 0    
  }
  def runme = OOPSI().check
}
