
import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Iterables {
  @ghost
  def test_setToList(set: Set[BigInt]) = {
    require(set.contains(1) && set.contains(2) && !set.contains(3))

    val res = set.toList
    set.toListPost(1)
    assert(res.contains(1))
    set.toListPost(2)
    assert(res.contains(2))
    set.toListPost(3)
    assert(!res.contains(3))
  }
  @ghost
  def test_setMap(set: Set[BigInt]) = {
    require(set.contains(1) && set.contains(2) && !set.contains(3))

    val f = ((x:BigInt) => x + 1)
    val res = set.map(f)

    set.mapPost1(f)(1)
    assert(res.contains(2))
    set.mapPost1(f)(2)
    assert(res.contains(3))
    if (res.contains(4)) {
      set.mapPost2[BigInt](f)(4)
      assert(false)
      check(!res.contains(4))
    }
    assert(!res.contains(4))
  }

  val oneToSix = Set[BigInt](1,2,3,4,5,6)
  @ghost
  def test_setFilter(set: Set[BigInt]) = {
    require((set & oneToSix) == oneToSix)

    val p = ((x:BigInt) => x < 4)
    val res = set.filter(p)
    set.filterPost(p)(1)
    assert(res.contains(1))
    set.filterPost(p)(2)
    assert(res.contains(2))
    set.filterPost(p)(3)
    assert(res.contains(3))
    set.filterPost(p)(4)
    assert(!res.contains(4))
    set.filterPost(p)(5)
    assert(!res.contains(5))
    set.filterPost(p)(6)
    assert(!res.contains(6))
  }
  @ghost
  def test_mapKeys(map: Map[Int, String]) = {
    require(map.contains(1) && map.contains(2) && !map.contains(3))

    val res = map.keys

    map.keysPost(1)
    assert(res.contains(1))
    map.keysPost(2)
    assert(res.contains(2))
    map.keysPost(3)
    assert(!res.contains(3))
  }
  @ghost
  def test_mapValues(map: Map[Int, String]) = {
    require(map.get(1) == Some("foo") && map.get(2) == Some("bar"))

    val res = map.values

    map.valuesPost1(1)
    assert(res.contains("foo"))
    map.valuesPost1(2)
    assert(res.contains("bar"))
  }
  @ghost
  def test_mapToList(map: Map[Int, String]) = {
    require(map.get(1) == Some("foo") && map.get(2) == Some("bar"))

    val res = map.toList

    map.toListPost(1)
    assert(res.contains((1, "foo")))
    map.toListPost(2)
    assert(res.contains((2, "bar")))
  }
}
