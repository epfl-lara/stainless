import stainless.lang.Quantifiers.*
import stainless.annotation.*
object ForallExistsTest:
  @ghost
  def eg =
    def pick1(x: BigInt) =
      require(0 <= x)
      val x4 = x + x + x + x
      val t1 = x4 + 1
      val t2 = t1 + 1
      {
        assert(x4 < t1)
        assert(x4 < t2)
        if t1 % 2 == 0 then
          assert(x4 < t1 && t1 % 2 == 0)
          ExistsThe(t1)((y: BigInt) => x4 < y && y % 2 == 0)
        else 
          assert(t1 % 2 == 1)
          assert(x4 < t2 && t2 % 2 == 0)
          ExistsThe(t2)((y: BigInt) => x4 < y && y % 2 == 0)
      }.ensuring((_:Unit) =>
         Exists((y: BigInt) => x4 < y && y % 2 == 0))

//    assert(forall((x:BigInt) => 
//      exist((y: BigInt) => (x + x + x + x) < y && y % 2 == 0)))
