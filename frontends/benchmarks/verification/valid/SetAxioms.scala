
import stainless.lang._
import stainless.collection._
import stainless.annotation._

object Iterables {

  @extern @pure
  def setToListAxiom[A](set: Set[A], a: A): Unit = {
    ()
  }.ensuring { _ => set.contains(a) == set.toList.contains(a) }

  def test_setToList(set: Set[BigInt]) = {
    require(set.contains(1) && set.contains(2) && !set.contains(3))

    val res = set.toList

    setToListAxiom[BigInt](set, 1)
    assert(res.contains(1))

    setToListAxiom[BigInt](set, 2)
    assert(res.contains(2))

    setToListAxiom[BigInt](set, 3)
    assert(!res.contains(3))
  }

  @extern @pure
  def setMapAxiom[A, B](set: Set[A], f: A => B, a: A): Unit = {
    ()
  }.ensuring { _ =>
    set.contains(a) ==> set.map(f).contains(f(a))
  }

  def test_setMap(set: Set[BigInt]) = {
    require(set.contains(1) && set.contains(2) && !set.contains(3))

    val res = set.map(_ + 1)

    setMapAxiom[BigInt, BigInt](set, _ + 1, 1)
    assert(res.contains(2))
    setMapAxiom[BigInt, BigInt](set, _ + 1, 2)
    assert(res.contains(3))
  }

  val oneToSix = Set[BigInt](1,2,3,4,5,6)

  @extern @pure
  def setFilterAxiom[A](set: Set[A], p: A => Boolean, a: A): Unit = {
    ()
  }.ensuring { _ =>
    if (set.contains(a) && p(a)) {
      set.filter(p).contains(a)
    } else {
      !set.filter(p).contains(a)
    }
  }

  def test_setFilter(set: Set[BigInt]) = {
    require((set & oneToSix) == oneToSix)

    val res = set.filter(_ < 4)

    setFilterAxiom[BigInt](set, _ < 4, 1)
    assert(res.contains(1))
    setFilterAxiom[BigInt](set, _ < 4, 2)
    assert(res.contains(2))
    setFilterAxiom[BigInt](set, _ < 4, 3)
    assert(res.contains(3))
    setFilterAxiom[BigInt](set, _ < 4, 4)
    assert(!res.contains(4))
    setFilterAxiom[BigInt](set, _ < 4, 5)
    assert(!res.contains(5))
    setFilterAxiom[BigInt](set, _ < 4, 6)
    assert(!res.contains(6))
    setFilterAxiom[BigInt](set, _ < 4, 7)
    assert(!res.contains(7))
  }

  // See https://github.com/epfl-lara/inox/issues/109
  // def test_setWithFilter(set: Set[BigInt]) = {
  //   require((set & oneToSix) == oneToSix)

  //   val res = for {
  //     x <- set
  //     if x < 4
  //   } yield x

  //   assert(res.contains(1))
  //   assert(res.contains(2))
  //   assert(res.contains(3))
  //   assert(!res.contains(4))
  //   assert(!res.contains(5))
  //   assert(!res.contains(6))
  // }
}
