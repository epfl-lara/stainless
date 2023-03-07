object i1379c {
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

  def smth(an: MyOption[Animal]): BigInt = an match {
    case MyBiggerDefault(a, b, c) => a.id + b.id + c.id
    case MySimpleDefault(a, b) => a.id + b.id
    case MySome(_) => 42
  }

  def test(a: Animal): Unit = {
    assert(smth(MyBiggerDefault(Cow(42), a, Cow(44))) != 86 + a.id)
  }
}