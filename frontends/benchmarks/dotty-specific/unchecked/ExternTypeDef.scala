
import stainless.lang._
import stainless.annotation._
import scala.annotation.meta.field

import scala.collection.concurrent.TrieMap

object ExternTypeDef {

  @extern
  opaque type AMap[A, B] = TrieMap[A, B]

  object AMap {
    @extern @pure
    def empty[K, V]: AMap[K, V] = {
      TrieMap.empty[K, V]
    }
  }

  def test = {
    val wrapper = AMap.empty[BigInt, String]
    wrapper == wrapper
  }.holds

}
