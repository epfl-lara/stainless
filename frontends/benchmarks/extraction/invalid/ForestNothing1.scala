import stainless.lang._
import stainless.annotation._

object ForestNothing1 {

  case class Tree(id: BigInt)

  // Not well formed ADT
  case class Forest(x: Tree, left: Forest, right: Forest)

  def what(f: Forest): Unit = {
    what(f.left)
  }.ensuring(_ => false)

  def theorem() = {
    val f: Forest = choose((x: Forest) => true)
    what(f)
    assert(false)
    ()
  }
}
