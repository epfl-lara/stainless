
import stainless.lang._
import stainless.annotation._
import scala.annotation.meta.field

import scala.collection.concurrent.TrieMap

object ExternField {

  case class TrieMapWrapper[K, V](
    @(extern @field)
    @(pure @field)
    theMap: TrieMap[K, V]
  ) {

    @extern @pure
    def contains(k: K): Boolean = {
      theMap contains k
    }

    @extern @pure
    def insert(k: K, v: V): TrieMapWrapper[K, V] = {
      TrieMapWrapper(theMap += (k -> v))
    } ensuring { _.contains(k) }

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
    val wrapper = TrieMapWrapper.empty[BigInt, BigInt]
    assert(!wrapper.contains(1))
    assert(wrapper.insert(1, 2).contains(1))
  }

}
