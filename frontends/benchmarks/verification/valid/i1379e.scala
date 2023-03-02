object i1379e {
  sealed abstract class MyOption[+T]
  case class MySome[+T](value: T) extends MyOption[T]
  sealed abstract class MyDefault extends MyOption[Nothing] {
    def a: BigInt
    def b: BigInt
  }
  case class MyBiggerDefault(a: BigInt, b: BigInt, c: BigInt) extends MyDefault
  case class MySimpleDefault(a: BigInt, b: BigInt) extends MyDefault

  trait Animal
  case class Cow(id: BigInt) extends Animal

  def smth1(an: MyOption[Animal]): BigInt = an match {
    case md: MyDefault => md.a + md.b
    case MySome(_) => 42
  }

  def test1(a: Animal): Unit = {
    assert(smth1(MyBiggerDefault(42, 43, 44)) == 85)
    assert(smth1(MySome(a)) == 42)
  }

  def smth2(an: MyOption[Animal]): BigInt = an match {
    case MyBiggerDefault(a, b, c) => a + b + c
    case md: MyDefault => md.a + md.b
    case MySome(_) => 42
  }

  def test2(a: Animal, md: MyDefault): Unit = {
    assert(smth2(MyBiggerDefault(42, 43, 44)) == 129)
    assert(smth2(MySimpleDefault(42, 43)) == 85)
    assert(smth2(MySome(a)) == 42)
  }
}