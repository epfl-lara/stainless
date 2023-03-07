object i1379f {
  sealed abstract class MyOption[+T]
  case class MySome[+T](value: T) extends MyOption[T]
  sealed abstract class MyDefault[+T] extends MyOption[T] {
    def a: T
    def b: T
  }
  case class MyBiggerDefault[+T](a: T, b: T, c: T) extends MyDefault[T]
  case class MySimpleDefault[+T](a: T, b: T) extends MyDefault[T]

  trait Animal {
    def id: BigInt
  }
  case class Cow(id: BigInt) extends Animal

  def smth1(an: MyOption[Animal]): BigInt = an match {
    case MyBiggerDefault(a, b, c) => a.id + b.id + c.id
    case MySimpleDefault(a, b) => a.id + b.id
    case MySome(_) => 42
  }

  def test1(a: Animal): Unit = {
    assert(smth1(MyBiggerDefault(Cow(42), Cow(43), Cow(44))) == 129)
    assert(smth1(MyBiggerDefault(Cow(42), a, Cow(44))) == 86 + a.id)
    assert(smth1(MySimpleDefault(Cow(42), Cow(43))) == 85)
    assert(smth1(MySimpleDefault(Cow(42), a)) == 42 +  a.id)
    assert(smth1(MySome(a)) == 42)
  }
}