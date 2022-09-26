import stainless._
import stainless.lang._
import stainless.annotation._

// TODO: This test case is originally about missing line numbers for plantThm postconditions.
// If/when integration tests also test for input, ensure this case to have the correct source info.
object i1295 {
  sealed trait State{
    def plant: Tree = {
      this match {
      case Baz(t1, t2) => {
          val kd1 = t1.plant
          val kd2 = t2.plant
          if(kd1.s == Foo && kd1.s == Foo){
              Node(Foo, kd1, kd2)
          }
          else{
              Leaf
          }
      }
      case _ => Leaf
      }
    }
  }
  case object Foo extends State
  case class Bar(s: State) extends State
  case class Baz(s1: State, s2: State) extends State

  sealed trait Tree {

    def s: State = this match {
      case Leaf => Baz(Foo, Foo)
      case Node(s, _, _) => s
    }

    def isFoo: Boolean = {
      this match{
        case Node(s, bkd1, bkd2) => {
          bkd1.isFoo && bkd2.isFoo &&
          bkd1.s == Foo && bkd2.s == Foo
        }
        case _ => false

      }
    }

  }
  case object Leaf extends Tree
  case class Node(s: State, bkd1: Tree, bkd2: Tree) extends Tree

  @opaque @pure
  def plantThm(s: State): Unit = {
    s match {
      case Foo => ()
      case Bar(t) => {
        plantThm(t)
      }
      case Baz(t1, t2) => {
        plantThm(t1)
        plantThm(t2)
      }
    }
  }.ensuring(
    s.plant.isFoo
  )
}