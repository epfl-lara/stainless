import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.Option._
import stainless.lang.StaticChecks._
import stainless.proof.check

object OpaqueEffectsExample {
  case class Cell(var value: Int) extends AnyHeapRef

  case class Leaf(data: Cell) extends Tree
  case class Branch(left: Tree, right: Tree) extends Tree
  sealed abstract class Tree {

    @ghost def repr: Set[AnyHeapRef] =
      this match {
        case Leaf(data) => Set[AnyHeapRef](data)
        case Branch(left, right) => left.repr ++ right.repr
        //totry: Set[AnyHeapRef]() 
      }
    @opaque
    def tmap(f: Int => Int): Unit = {
      reads(repr)
      modifies(repr)
      decreases(this)

      this match {
        case Leaf(data) =>
          data.value = f(data.value)
        case Branch(left, right) =>
          left.tmap(f)
          right.tmap(f)
      }
    }
  }
  def test(t: Tree, c: Cell) = {
    require(c.value == 0 && !t.repr.contains(c))
    reads(t.repr ++ Set[AnyHeapRef](c))
    modifies(t.repr)
    
    t.tmap(x => (x | 1))
  } ensuring(_ => c.value == 0)
}
