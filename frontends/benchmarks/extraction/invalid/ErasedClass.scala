object ErasedClass {
  erased case class MyClass(x: BigInt, y: BigInt)

  def buildClass(x: BigInt) = MyClass(x, x)
}
