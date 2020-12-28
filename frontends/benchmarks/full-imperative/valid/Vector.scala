import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.collection.ListSpecs._

object Vector {
  case class Box(var value: BigInt) extends AnyHeapRef

  case class Vector(var data: List[Box]) extends AnyHeapRef {
    def toList: List[Box] = {
      reads(Set(this))
      data.reverse
    }

    def size: BigInt = {
      reads(Set(this))
      data.size
    } ensuring { _ >= 0 }

    def apply(index: BigInt): Box = {
      require(0 <= index && index < data.size)
      reads(Set(this))
      data(data.size - index - 1)
    }

    @allocates
    def append(x: BigInt): Unit = {
      reads(Set(this))
      modifies(Set(this))
      val box = Box(x)
      assert(snocLast(data, box))
      data = Cons(box, data)
    } ensuring { _ =>
      toList.last == x &&
      old(toList) == toList.init
    }
  }
}
