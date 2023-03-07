object i1379d {
  sealed abstract class MyOption[+T]
  case class MySome[+T](value: T) extends MyOption[T]
  case class MyDefault[+T](a: T, b: T) extends MyOption[T]

  trait Animal {
    def id: BigInt
  }
  case class Cow(id: BigInt) extends Animal

  def smth1(an: MyOption[Animal]): BigInt = an match {
    case MyDefault(a, b) => a.id + b.id
    case MySome(_) => 42
    case _ => 123
  }

  def test1(a: Animal): Unit = {
    assert(smth1(MyDefault(Cow(42), Cow(43))) == 85)
    assert(smth1(MySome(a)) == 42)
  }

  def smth2(an: MyOption[Animal]): BigInt = an match {
    case MyDefault(Cow(id), b) => id + b.id
    case MyDefault(a, b) => a.id + b.id - 1
    case MySome(_) => 42
    case _ => 123
  }

  def test2(a: Animal): Unit = {
    require(a match {
      case Cow(_) => false
      case _ => true
    })
    assert(smth2(MyDefault(Cow(42), Cow(43))) == 85)
    assert(smth2(MyDefault(a, Cow(43))) == a.id + 43 - 1)
    assert(smth2(MySome(a)) == 42)
  }

  def smth3(an: MyOption[Animal]): BigInt = an match {
    case MyDefault(Cow(id1), Cow(id2)) => id1 + id2
    case MyDefault(a, b) => a.id + b.id - 1
    case MySome(_) => 42
    case _ => 123
  }

  def test3(a: Animal, b: Animal): Unit = {
    require((a, b) match {
      case (Cow(_), Cow(_)) => false
      case _ => true
    })
    assert(smth3(MyDefault(Cow(42), Cow(43))) == 85)
    assert(smth3(MyDefault(a, b)) == a.id + b.id - 1)
    assert(smth3(MySome(a)) == 42)
  }
}