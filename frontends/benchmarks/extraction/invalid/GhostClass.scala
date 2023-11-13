import stainless.annotation._
object GhostClass {
  @ghost
  case class MyClass(x: BigInt, y: BigInt)

  def buildClass(x: BigInt) = MyClass(x, x)
}