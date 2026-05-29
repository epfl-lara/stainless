package asInstanceOfUnbox
object A {
  val x: Any = 1
  val y: Boolean = x.asInstanceOf[Boolean]
}