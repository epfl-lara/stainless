
object typedefs {

  case class Stuff[A](x: A)

  type Hello[World] = World

  type Foo = BigInt

  type Bar = Hello[BigInt]

  type IntStuff = Stuff[BigInt]

  type SomeStuff[Box] = Stuff[(Box, Box)]

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


}
