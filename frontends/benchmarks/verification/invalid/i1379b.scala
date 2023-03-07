object i1379b {
  sealed abstract class MyOption[+T]
  case class MySome[+T](value: T) extends MyOption[T]
  case class MyDefault(x: BigInt) extends MyOption[Nothing]

  trait Animal
  case class Cow(id: BigInt) extends Animal

  def smth(an: MyOption[Animal]): BigInt = an match {
    case MyDefault(xyz) => xyz
    case MySome(_) => 42
  }

  def test(a: Animal): Unit = {
    assert(smth(MyDefault(43)) != 43)
  }
}