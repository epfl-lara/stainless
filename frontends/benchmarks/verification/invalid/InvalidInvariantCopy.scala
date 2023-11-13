object InvalidInvariantCopy {
  case class MyClass(x: BigInt) {
    require(x >= 0)
  }

  def copyClass(mc: MyClass, x: BigInt): MyClass = mc.copy(x + x)
}