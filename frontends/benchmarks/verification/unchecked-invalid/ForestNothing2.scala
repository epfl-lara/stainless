import stainless.lang._
import stainless.proof._
import stainless.annotation._

object ForestNothing2 {

  case class Tree(id: BigInt)

  // A variant of ForestNothing1 that does not get rejected to due well-formedness reasons.
  // We "trick" the sort well-formedness check by adding a dummy leaf JustTree that is actually
  // never part of the forest (thanks to the invariant).
  sealed trait Forest {
    require(this match {
      case TreeAndForest(_, _) => true
      case JustTree(_) => false
    })
  }
  case class TreeAndForest(head: Tree, tail: Forest) extends Forest
  case class JustTree(t: Tree) extends Forest

  def what(f: Forest): Boolean = {
    f match {
      case TreeAndForest(_, t) =>
        what(t)
      case JustTree(_) =>
        check(false)
        false
    }
 }.ensuring(_ => false)

  def chooseFn[A, B]: A => B = choose[A => B](f => true)

  def mkForest: Forest = {
    // choose((x: Forest) => true) rejected due to quantification not fitting
    // in supported fragment (due to ADT invariant)
    val fn = chooseFn[BigInt, Forest]
    fn(42)
  }

  def theorem: Unit = {
    val f: Forest = mkForest
    what(f)
    assert(false)
    ()
  }
}
