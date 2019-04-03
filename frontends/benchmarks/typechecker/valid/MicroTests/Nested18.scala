object Nested18 {

  def test(a: BigInt): BigInt = {
    require(a > 0)
    def f(b: BigInt): BigInt = {
      def g(c: BigInt): BigInt = {
        require(a > 0)
        c
      }
      g(b)
    }
    f(12)
  }

}
