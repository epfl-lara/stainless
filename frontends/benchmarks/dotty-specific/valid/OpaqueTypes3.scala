object OpaqueTypes3 {
  opaque type Tagged[T] <: BigInt = BigInt
  object Tagged {
    def apply[T](b: BigInt): Tagged[T] = {
      require(b >= 0)
      b
    }
  }
}

// Like OpaqueTypes2, but with an applied (parameterized) opaque type
// constructor used outside its defining scope.
object OpaqueTypes3Use {
  import OpaqueTypes3.*
  def test(p: Tagged[Int], q: Tagged[Int]): BigInt = {
    p + q
  }

  def test2: BigInt = Tagged[Int](BigInt(1)) + Tagged[Int](BigInt(2))
}
