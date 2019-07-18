object MatchGuard {
  sealed abstract class Nat
  case object Zero extends Nat
  case class Succ(n: Nat) extends Nat

  def f(n: Nat): Boolean = n match {
    case Zero => true
    case Succ(n2) if { assert(n == Succ(n2)); true } => true
    case _ => true
  }
}
