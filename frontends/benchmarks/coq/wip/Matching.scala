object Matching {

  sealed abstract class X
  case class A() extends X
  case class B() extends X

  def theorem(x: X) = x match {
    case A() => assert(x == A())
    case B() => assert(x == A())
  }
}
