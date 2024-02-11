object InnerFuns {
  def myOuterFun1(x: BigInt): BigInt = {
    def myInnerFun1_1(x: BigInt): BigInt = {
      def myInnerInnerFun1_1(x: BigInt): BigInt = {
        def myInnerInnerInnerFun1_1(x: BigInt): BigInt = x
        x
      }
      def myInnerInnerFun1_2(x: BigInt): BigInt = x
      x
    }
    def myInnerFun1_2(x: BigInt): BigInt = x
    x
  }


  def myOuterFun2(x: BigInt): BigInt = {
    def myInnerFun2_1(x: BigInt): BigInt = {
      def myInnerInnerFun2_1(x: BigInt): BigInt = {
        def myInnerInnerInnerFun2_1(x: BigInt): BigInt = x
        x
      }
      def myInnerInnerFun2_2(x: BigInt): BigInt = x
      x
    }
    def myInnerFun2_2(x: BigInt): BigInt = x
    x
  }
}