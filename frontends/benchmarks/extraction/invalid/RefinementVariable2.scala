package variable2

case class A(var x: Int):
  def getX(): Int = x
  def isXPos(): Boolean = getX() > 0
  def f(): Unit =
    var err: Int with (err > 0) == isXPos() = x
    ()