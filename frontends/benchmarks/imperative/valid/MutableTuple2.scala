import stainless.lang._
import stainless.annotation._

object MutableTuple2 {
  case class Foo(var value: BigInt)
  case class Bar(var value: BigInt)

  def t1(pair: (Foo, Bar)): BigInt = {
    pair._1.value = 1
    assert(pair._1.value == 1)
    pair._2.value
  }

  def t3(): (Foo, Bar) = {
    val bar = Bar(1)
    val foo = Foo(2)
    (foo, bar)
  }

  def t4() = {
    val pair = t3()
    pair._2.value = 100

    val pair1Alias = pair._1
    val pair2Alias = pair._2

    val x = t1((pair._1, pair._2))
    assert(x == 100)
    assert(pair._1.value == 1)
    assert(pair._2.value == 100)
    assert(pair1Alias.value == 1)
    assert(pair2Alias.value == 100)
  }

  def t5() = {
    val pair = t3()
    pair._2.value = 100

    val pair1Alias = pair._1
    val pair2Alias = pair._2

    val x = t1((pair1Alias, pair2Alias)) // (ReplacementEffect(pair._1.value (pair de t1, pas la var local),List((ReplacementEffect(pair1Alias.value),None)))
    assert(x == 100)
    assert(pair._1.value == 1)
    assert(pair._2.value == 100)
    assert(pair1Alias.value == 1)
    assert(pair2Alias.value == 100)
  }
}
