import stainless._
import stainless.lang._
import stainless.annotation._

object TargetMutation4 {

  case class Box(var value: Int)

  def mutate(b: Box, v: Int): Unit = {
    b.value = v
  }

  def h1(x: Box, cond: Boolean): Unit = {
    val oldX = x.value
    val y = if (cond) x else Box(1234)
    y.value = 456
    assert(y.value == 456)
    assert(cond ==> (x.value == 456))
    assert(!cond ==> (x.value == oldX))
  }

  def h1Mutate(x: Box, cond: Boolean): Unit = {
    val oldX = x.value
    val y = if (cond) x else Box(1234)
    mutate(y, 456)
    assert(y.value == 456)
    assert(cond ==> (x.value == 456))
    assert(!cond ==> (x.value == oldX))
  }

  def h2(x: Box, z: Box, cond1: Boolean, cond2: Boolean): Unit = {
    val oldX = x.value
    val oldZ = z.value
    val y = if (cond1) x else if (cond2) Box(1234) else z
    y.value = 456
    assert(y.value == 456)
    assert(cond1 ==> (x.value == 456))
    assert(!cond1 ==> (x.value == oldX))
    assert((!cond1 && !cond2) ==> (z.value == 456))
    assert((cond1 || cond2) ==> (z.value == oldZ))
  }

  def h2Mutate(x: Box, z: Box, cond1: Boolean, cond2: Boolean): Unit = {
    val oldX = x.value
    val oldZ = z.value
    val y = if (cond1) x else if (cond2) Box(1234) else z
    mutate(y, 456)
    assert(y.value == 456)
    assert(cond1 ==> (x.value == 456))
    assert(!cond1 ==> (x.value == oldX))
    assert((!cond1 && !cond2) ==> (z.value == 456))
    assert((cond1 || cond2) ==> (z.value == oldZ))
  }

  def h3(): Unit = {
    val y = Box(123)
    val z = y

    z.value = 432
    assert(y.value == 432)
    assert(z.value == 432)

    y.value = 111
    assert(y.value == 111)
    assert(z.value == 111)
  }

  def h3Mutate(): Unit = {
    val y = Box(123)
    val z = y

    mutate(z, 432)
    assert(y.value == 432)
    assert(z.value == 432)

    mutate(y, 111)
    assert(y.value == 111)
    assert(z.value == 111)
  }
}
