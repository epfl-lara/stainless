import stainless.lang._
import stainless.annotation._

object MutableTuple {
  case class Foo(var value: BigInt)
  case class Bar(var value: BigInt)

  def t1(pair: (Foo, Bar)): BigInt = {
    pair._1.value = 1
    assert(pair._1.value == 1)
    pair._2.value
  }

  def t2() = {
    val pair =  (Foo(1), Foo(2), Foo(3))
    val secondFoo = pair._2
    secondFoo.value = 4
    assert(pair == (Foo(1), Foo(4), Foo(3)))
    assert(pair._2.value == secondFoo.value)

    pair._2.value = 6
    assert(pair == (Foo(1), Foo(6), Foo(3)))
    assert(pair._2.value == secondFoo.value)
  }

  def t3(): (Foo, Bar) = {
    val bar = Bar(10)
    val foo = Foo(20)
    (foo, bar)
  }

  def t4() = {
    val pair = t3()
    pair._2.value = 100

    val x = t1((pair._1, pair._2))
    assert(x == 100)
    assert(pair._1.value == 1)
    assert(pair._2.value == 100)
  }
}
