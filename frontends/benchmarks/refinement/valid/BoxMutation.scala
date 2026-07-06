package boxMutation

object A:
  case class Box(var x: Int):
    def getX() : Int = x
    def foo() : {r : Boolean with r == (getX() > 0)} = x > 0

object Mutation2:
  def test() : Unit =
    val b = A.Box(1)
    assert(b.foo())
    b.x = -1
    assert(!b.foo())
