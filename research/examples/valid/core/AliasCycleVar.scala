import stainless.lang._

object AliasCycleVar {
  sealed abstract class BOrNone
  case class NoB() extends BOrNone
  case class SomeB(b: B) extends BOrNone

  case class A(var link: BOrNone)
  case class B(link: A)

  def f: Unit = {
    val a = A(NoB())
    var b = B(a)

    a.link = SomeB(b)
  }
}
