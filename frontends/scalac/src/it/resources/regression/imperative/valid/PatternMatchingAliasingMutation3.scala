object PatternMatchingAliasingMutation3 {

  case class MutableObject(var x: Int)

  abstract class A
  case class B(m: MutableObject) extends A
  case class C(m: MutableObject) extends A

  def updateValue(a: A, newVal: Int): Unit = a match {
    case B(m) => m.x = newVal
    case C(m) => m.x = newVal
  }

  def f(): Int = {
    val b = B(MutableObject(10))
    updateValue(b, 15)
    b.m.x
  } ensuring(_ == 15)
}
