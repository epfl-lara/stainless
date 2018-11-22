
import stainless.lang._
import stainless.annotation._

import scala.collection.immutable.HashMap

object ExternFieldPure {

  case class MapWrapper[K, V](
    @extern @pure
    theMap: HashMap[K, V]
  ) {

    @extern @pure
    def contains(k: K): Boolean = {
      theMap contains k
    }

    @extern @pure
    def insert(k: K, v: V): MapWrapper[K, V] = {
      MapWrapper(theMap + (k -> v))
    } ensuring { _.contains(k) }

    @extern @pure
    def apply(k: K): V = {
      require(contains(k))
      theMap(k)
    }
  }

  object MapWrapper {
    @extern
    def empty[K, V]: MapWrapper[K, V] = {
      MapWrapper(HashMap.empty[K, V])
    } ensuring { res =>
      forall((k: K) => !res.contains(k))
    }
  }

  def test = {
    val wrapper = MapWrapper.empty[BigInt, BigInt]
    assert(!wrapper.contains(1))
    assert(wrapper.insert(1, 2).contains(1))
  }

}
