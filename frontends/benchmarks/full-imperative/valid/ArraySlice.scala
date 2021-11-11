import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.proof._
import stainless.lang.StaticChecks._

object ArraySliceExample {
  def updateSizeLemma[T](xs: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i < xs.size)
    decreases(xs)

    xs match {
      case Nil() => true
      case Cons(x, xs) => if (i == 0) true else updateSizeLemma[T](xs, i - 1, y)
    }

    xs.updated(i, y).size == xs.size
  }.holds

  final case class SArray[T](var content: List[T]) extends AnyHeapRef {
    def fill(n: BigInt)(default: T): Unit = {
      // should become a constructor eventually instead of a method
      // Creates visible sharing, so needs support for allocator
      reads(Set(this))
      require(0 <= n)
      modifies(Set(this))
      content = List.fill(n)(default)
    } ensuring { _ => content.size == n }

    def apply(i: BigInt): T = {
      reads(Set(this))
      require(0 <= i && i < content.size)
      content(i)
    }

    def update(i: BigInt, v: T): Unit = {
      reads(Set(this))
      require(0 <= i && i < content.size)
      modifies(Set(this))
      updateSizeLemma(content, i, v)
      content = content.updated(i, v)
    } ensuring { _ => content.size == old(content.size) }
  }

  final case class ArraySlice[T](a: SArray[T], from: BigInt, until: BigInt) {
    // these slices retain their original indices but preclude access outside of range
    require(0 <= from && from <= until)

    def valid: Boolean = { // this method aspires to become part of the above `require`
      reads(Set(a))
      until <= a.content.size
    }

    def apply(i: BigInt): T = {
      reads(Set(a))
      require(from <= i && i < until && valid)

      a(i)
    }

    def update(i: BigInt, v: T): Unit = {
      reads(Set(a))
      require(from <= i && i < until && valid)
      modifies(Set(a))

      a(i) = v
    } ensuring { _ => valid }

    def reSlice(from1: BigInt, until1: BigInt): ArraySlice[T] = {
      reads(Set(a))
      require(from <= from1 && from1 <= until1 && until1 <= until && valid)
      ArraySlice[T](a, from1, until1)
    }
  }


  @extern
  def pr(s: String): Unit = {
    println(s)
  }

  // @extern // remove the `@extern` for some hard VCs
  def testSlices(a: SArray[String]): Unit = {
    reads(Set(a))
    modifies(Set(a))
    a.fill(5)("")
    a(3) = "s3"
    a(4) = "s4"
    a(0) = "s0"
    a(2) = "s2"
    a(1) = "s1"
    val slice14 = ArraySlice(a, 1, 4)
    assert(slice14.valid)
    val slice23 = slice14.reSlice(2, 3)
    pr("slice23(2) = " + slice23(2))
    slice14(2) = "42"
    pr("slice23(2) = " + slice23(2))
  }

  @extern
  def main(args: Array[String]): Unit = {
    testSlices(SArray[String](List[String]()))
  }
}
