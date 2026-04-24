package asInstanceOfUnbox

object A {
  val x: Any = true
  val y: Boolean = x.asInstanceOf[Boolean]
}