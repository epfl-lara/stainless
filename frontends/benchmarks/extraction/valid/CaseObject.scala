case class S()

abstract class A
case object Main extends A {
  val s: S = S()

  def f(x: S): S = x match {
    case S() => S()
    case _ => s
  }    
}
