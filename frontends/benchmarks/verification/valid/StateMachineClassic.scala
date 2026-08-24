import stainless.lang._
import stainless.annotation._
import stainless.collection._

object StateMachineClassic {
  case class StateMachine[State,Letter](
    initial: State, 
    next: (State, Letter) => Option[State],
    isFinal: State => Boolean) 
  {
    final def contains(w0: List[Letter]): Boolean = {
      def rec(s: State, w: List[Letter]): Boolean = w match {
        case Nil() => isFinal(s)
        case Cons(l, ls) => next(s, l) match {
          case Some(s1) => rec(s1, ls)
          case None() => false
        }
      }
      rec(initial, w0)
    }
  }

  sealed abstract class MyState
  case object A extends MyState
  case object B extends MyState

  sealed abstract class MyLetter
  case object L1 extends MyLetter
  case object L2 extends MyLetter

  def myNext(s: MyState, l: MyLetter): Option[MyState] = (s, l) match {
    case (A, L1) => Some(A)
    case (A, L2) => Some(B)
    case (B, L2) => Some(A)
    case _ => None()
  }

  // Recognizes the language: (L1* L2 L2)* L2
  val MyMachine = StateMachine[MyState, MyLetter](
    initial = A,
    isFinal = (s: MyState) => { s == B },
    next = myNext)

  def tests() = {
    assert(MyMachine.contains(List(L1, L1, L2, L2, L1, L2)))
    assert(!MyMachine.contains(List(L1, L1, L2, L1, L2)))
  }
}
