import stainless._
import stainless.lang._

// Similar to i1251 test cases, except we directly mutate the fields
object TargetMutation1 {

  case class Box(var value: Int)
  case class BBox(var f: Box)
  case class BBBox(var ff1: BBox, var ff2: BBox)
  case class BBBBox(var fff: BBBox)

  def h1(b1: Box, b2: Box, b3: Box, cond1: Boolean, cond2: Boolean): Unit = {
    val b1Old = b1.value
    val b2Old = b2.value
    val b3Old = b3.value

    val c = if (cond1) b1 else b2
    val cOld = c.value
    val cAlias = c
    val d = if (cond2) c else b3

    d.value = 123

    assert(d.value == 123)

    assert(cond2 ==> (c.value == 123))
    assert(!cond2 ==> (c.value == cOld))
    assert(cond2 ==> (cAlias.value == 123))
    assert(!cond2 ==> (cAlias.value == cOld))

    assert((cond2 && cond1) ==> (b1.value == 123))
    assert(!cond1 ==> (b1.value == b1Old))

    assert((cond2 && !cond1) ==> (b2.value == 123))
    assert(cond1 ==> (b2.value == b2Old))

    assert(!cond2 ==> (b3.value == 123))
    assert(cond2 ==> (b3.value == b3Old))
  }

  def h2(b1: Box, b2: Box, cond1: Boolean, cond2: Boolean): Unit = {
    val b1Old = b1.value
    val b2Old = b2.value

    val c = if (cond1) b1 else b2
    val cOld = c.value
    val cAlias = c
    // Similar to h1, but the `else` returns b1
    val d = if (cond2) c else b1

    d.value = 123

    assert(d.value == 123)

    // Note that even if we have !cond2, we still end up mutating c if we have cond1
    assert((cond2 || cond1) ==> (c.value == 123))
    assert((!cond2 && !cond1) ==> (c.value == cOld))
    assert((cond2 || cond1) ==> (cAlias.value == 123))
    assert((!cond2 && !cond1) ==> (cAlias.value == cOld))

    assert((!cond2 || cond1) ==> (b1.value == 123))
    assert((cond2 && !cond1) ==> (b1.value == b1Old))

    assert((cond2 && !cond1) ==> (b2.value == 123))
    assert(cond1 ==> (b2.value == b2Old))
  }

  def h3(b1: Box, b2: Box, b3: Box, cond1: Boolean, cond2: Boolean): Unit = {
    val b1Old = b1.value
    val b2Old = b2.value
    val b3Old = b3.value

    val c = if (cond1) b1 else b2
    val cOld = c.value
    val cAlias = c
    val d = if (cond2) c else b3

    cAlias.value = 123

    assert(cond2 ==> (d.value == 123))
    assert(!cond2 ==> (d.value == b3.value))

    assert(c.value == 123)
    assert(cAlias.value == 123)

    assert(cond1 ==> (b1.value == 123))
    assert(!cond1 ==> (b1.value == b1Old))

    assert(!cond1 ==> (b2.value == 123))
    assert(cond1 ==> (b2.value == b2Old))

    assert(b3.value == b3Old)
  }

  // wwwwhhhhaaaatttt    ddddoooo    yyyyoooouuuu    mmmmeeeeaaaannnn    bbbbyyyy    """"nnnnooootttt    ccccrrrreeeeaaaattttiiiivvvveeee""""????
  def hhhh1(bbbb1: BBBBox, bbbb2: BBBBox, bbbb3: BBBBox, cond1: Boolean, cond2: Boolean, cond3: Boolean): Unit = {
    val b1Old = bbbb1.fff.ff1.f.value
    val b2Old = bbbb2.fff.ff1.f.value
    val b3Old = bbbb3.fff.ff1.f.value

    val cccc = if (cond1) bbbb1 else bbbb2
    val ddd = if (cond2) cccc.fff else bbbb3.fff
    val ee = if (cond3) ddd.ff1 else ddd.ff2

    ee.f.value = 123
    assert(ee.f.value == 123)

    assert(cond3 ==> ((ddd.ff1.f.value == 123) &&
                     ((cond2 ==> ((bbbb3.fff.ff1.f.value == b3Old && cccc.fff.ff1.f.value == 123) &&
                                 (cond1 ==> (bbbb1.fff.ff1.f.value == 123 && bbbb2.fff.ff1.f.value == b2Old)))))))

    ddd.ff1.f.value = 456
    assert(ddd.ff1.f.value == 456)
    assert(!cond3 ==> (ee.f.value == 123))
    assert(cond3 ==> (ee.f.value == 456))
  }
}
