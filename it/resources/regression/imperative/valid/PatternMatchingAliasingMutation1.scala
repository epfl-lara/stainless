object PatternMatchingAliasingMutation1 {

  abstract class A
  case class B(var x: Int) extends A
  case class C(var y: Int) extends A

  def updateValue(a: A, newVal: Int): Unit = a match {
    case (b: B) => b.x = newVal
    case (c: C) => c.y = newVal
  }

  def f(): Int = {
    val b = B(10)
    updateValue(b, 15)
    b.x
  } ensuring(_ == 15)
}
