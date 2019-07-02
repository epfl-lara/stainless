import stainless.lang._
import stainless.annotation._
import stainless.collection._

object StateMachine {
  sealed trait StateMachine {
    type State
    type Letter

    def initial: State
    def next(s: State, l: Letter): Option[State]
    def isFinal(s: State): Boolean

    @extern @pure
    final def isEmpty: Boolean = ???

    @extern @pure
    final def isTotal: Boolean = ???

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

    @extern @pure
    final def subsetOf(other: StateMachine): Boolean = ???
  }

  sealed abstract class MyState
  case object A extends MyState
  case object B extends MyState

  sealed abstract class MyLetter
  case object L1 extends MyLetter
  case object L2 extends MyLetter

  // Recognizes the language: (L1* L2 L2)* L2
  case object MyMachine extends StateMachine {
    type State = MyState
    type Letter = MyLetter
    def initial = A
    def isFinal(s: State) = { s == B }
    def next(s: State, l: Letter): Option[State] = (s, l) match {
      case (A, L1) => Some(A)
      case (A, L2) => Some(B)
      case (B, L2) => Some(A)
      case _ => None()
    }
  }

  def tests() = {
    // assert(!MyMachine.isEmpty)
    // assert(!MyMachine.isTotal)
    assert(MyMachine.contains(List(L1, L1, L2, L2, L1, L2)))
    assert(!MyMachine.contains(List(L1, L1, L2, L1, L2)))
    // assert(MyMachine.contains(List(L1, L2)))
  }
}
