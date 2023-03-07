object i1379a {
  sealed abstract class MyOption[+T]
  case class MySome[+T](value: T) extends MyOption[T]
  case object MyNone extends MyOption[Nothing]

  trait Animal
  case class Cow(id: BigInt) extends Animal

  def smth(an: MyOption[Animal]): BigInt = an match {
    case MyNone => 0
    case MySome(c: Cow) => 41
    case MySome(animal) => 42
    case _ => 0
  }

  def test(animal: Animal): Unit = {
    assert(smth(MyNone) == 0)
    assert(smth(MySome(Cow(1))) == 41)
    assert(animal match {
      case c: Cow => smth(MySome(animal)) == 41
      case _ => smth(MySome(animal)) == 42
    })
  }
}