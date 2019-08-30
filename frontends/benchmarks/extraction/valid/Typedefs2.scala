
object Typedefs2 {

  case class Stuff[A](x: A)

  type Hello[World] = World

  type Foo = BigInt

  type Bar = Hello[BigInt]

  type IntStuff = Stuff[BigInt]

  type SomeStuff[A, B] = Stuff[(A, B)]

  // type PositiveInt = { x: Int => x >= 0 }

  def hello(x: BigInt): Hello[BigInt] = {
    assert(x == BigInt(0))
    x
  }

  def foo(x: Foo): BigInt = {
    assert(x == BigInt(0))
    x
  }

  def bar(x: Hello[BigInt]): BigInt = {
    assert(x == BigInt(0))
    x
  }

  def intStuff(a: IntStuff): BigInt = {
    assert(a.x == BigInt(0))
    a.x
  }

  def someStuff(a: SomeStuff[BigInt, Hello[BigInt]]): BigInt = {
    val res = a.x._1 + a.x._2
    assert(res == BigInt(0))
    res
  }

  // def takePos(x: PositiveInt): Int = {
  //   x
  // } ensuring { _ >= 0 }

}
