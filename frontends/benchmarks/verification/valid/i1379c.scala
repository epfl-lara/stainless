object i1379c {
  sealed abstract class MyOption[+T]
  case class MySome[+T](value: T) extends MyOption[T]
  case class MyDefault(a: BigInt, b: BigInt) extends MyOption[Nothing]

  trait Animal
  case class Cow(id: BigInt) extends Animal

  def smth(an: MyOption[Animal]): BigInt = an match {
    case MyDefault(a, b) => a + b
    case MySome(_) => 42
  }

  def test(a: Animal): Unit = {
    assert(smth(MyDefault(42, 43)) == 85)
    assert(smth(MySome(a)) == 42)
  }
}