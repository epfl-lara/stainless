import stainless._
import stainless.lang._

// Similar to i1251 test cases, except we directly perform field & arrays mutations
object TargetMutation2 {

  case class Box(var value: Int)
  case class BBox(var f: Box)
  case class BBBox(var ff1: Array[BBox], var ff2: BBox)
  case class BBBBox(var fff: BBBox)

  def hhhh1(bbbb1: BBBBox, bbbb2: BBBBox, bbbb3: BBBBox, cond1: Boolean, cond2: Boolean, cond3: Boolean, i: Int, j: Int): Unit = {
    require(0 <= i && i < bbbb1.fff.ff1.length)
    require(0 <= i && i < bbbb2.fff.ff1.length)
    require(0 <= i && i < bbbb3.fff.ff1.length)
    require(0 <= j && j < bbbb1.fff.ff1.length)
    require(0 <= j && j < bbbb2.fff.ff1.length)
    require(0 <= j && j < bbbb3.fff.ff1.length)

    val b1Old1i = bbbb1.fff.ff1(i).f.value
    val b1Old1j = bbbb1.fff.ff1(j).f.value
    val b1Old2 = bbbb1.fff.ff2.f.value
    val b2Old1i = bbbb2.fff.ff1(i).f.value
    val b2Old1j = bbbb2.fff.ff1(j).f.value
    val b2Old2 = bbbb2.fff.ff2.f.value
    val b3Old1i = bbbb3.fff.ff1(i).f.value
    val b3Old1j = bbbb3.fff.ff1(j).f.value
    val b3Old2 = bbbb3.fff.ff2.f.value

    val cccc = if (cond1) bbbb1 else bbbb2
    val ddd = if (cond2) cccc.fff else bbbb3.fff
    val ee = if (cond3) ddd.ff1(i) else ddd.ff1(j)

    ee.f.value = 123
    assert(ee.f.value == 123)

    assert(bbbb1.fff.ff2.f.value == b1Old2)
    assert(bbbb2.fff.ff2.f.value == b2Old2)
    assert(bbbb3.fff.ff2.f.value == b3Old2)

    assert((cond3 && i != j) ==> (bbbb1.fff.ff1(j).f.value == b1Old1j))
    assert((cond3 && i != j) ==> (bbbb2.fff.ff1(j).f.value == b2Old1j))
    assert((cond3 && i != j) ==> (bbbb3.fff.ff1(j).f.value == b3Old1j))

    assert(cond3 ==> (ddd.ff1(i).f.value == 123))
    assert((cond3 && cond2 && !cond1) ==> (bbbb2.fff.ff1(i).f.value == 123 && bbbb1.fff.ff1(i).f.value == b1Old1i))

    bbbb1.fff.ff1(j).f.value = 456
    assert(cond2 ==> (bbbb3.fff.ff1(j).f.value == b3Old1j))
  }

  def h2Replace(arr1: Array[Box], arr2: Array[Box], cond: Boolean, i: Int, j: Int): Unit = {
    require(0 <= i && i < arr1.length && i < arr2.length)
    require(0 <= j && j < arr1.length && j < arr2.length)

    val old1i = arr1(i).value
    val old1j = arr1(j).value
    val old2i = arr2(i).value
    val old2j = arr2(j).value

    val arr = if (cond) arr1 else arr2

    arr(i) = Box(456)

    assert((i != j) ==> (arr1(j).value == old1j && arr2(j).value == old2j))
    assert(cond ==> (arr2(i).value == old2i && arr2(j).value == old2j))
    assert(cond ==> (arr1(i).value == 456))
    assert(!cond ==> (arr1(i).value == old1i && arr1(j).value == old1j))
    assert(!cond ==> (arr2(i).value == 456))
  }

  def h2Modify(arr1: Array[Box], arr2: Array[Box], cond: Boolean, i: Int, j: Int): Unit = {
    require(0 <= i && i < arr1.length && i < arr2.length)
    require(0 <= j && j < arr1.length && j < arr2.length)

    val old1i = arr1(i).value
    val old1j = arr1(j).value
    val old2i = arr2(i).value
    val old2j = arr2(j).value

    val arr = if (cond) arr1 else arr2

    arr(i).value = 456

    assert((i != j) ==> (arr1(j).value == old1j && arr2(j).value == old2j))
    assert(cond ==> (arr2(i).value == old2i && arr2(j).value == old2j))
    assert(cond ==> (arr1(i).value == 456))
    assert(!cond ==> (arr1(i).value == old1i && arr1(j).value == old1j))
    assert(!cond ==> (arr2(i).value == 456))
  }
}
