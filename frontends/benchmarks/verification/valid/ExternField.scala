
import stainless.lang._
import stainless.annotation._
import scala.annotation.meta.field

import scala.collection.concurrent.TrieMap

object ExternField {

  case class TrieMapWrapper[K, V](
    @extern
    theMap: TrieMap[K, V]
  ) {

    @extern @pure
    def contains(k: K): Boolean = {
      theMap contains k
    }

    @extern
    def insert(k: K, v: V): Unit = {
      theMap.update(k, v)
    } ensuring {
      this.contains(k) &&
      this.apply(k) == v
    }

    @extern @pure
    def apply(k: K): V = {
      require(contains(k))
      theMap(k)
    }
  }

  object TrieMapWrapper {
    @extern @pure
    def empty[K, V]: TrieMapWrapper[K, V] = {
      TrieMapWrapper(TrieMap.empty[K, V])
    } ensuring { res =>
      forall((k: K) => !res.contains(k))
    }
  }

  def test = {
    val wrapper = TrieMapWrapper.empty[BigInt, String]
    assert(!wrapper.contains(42))
    wrapper.insert(42, "Hello")
    assert(wrapper.contains(42))
    assert(wrapper(42) == "Hello")
  }

}
