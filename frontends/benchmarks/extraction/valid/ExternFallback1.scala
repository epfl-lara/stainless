import stainless.lang._
import stainless.annotation._

object ExternFallback1 {

  import scala.collection.concurrent.TrieMap

  @extern @pure
  def getTrieMap(x: BigInt): TrieMap[BigInt, String] = TrieMap.empty

  @extern
  def setTrieMap(trie: TrieMap[BigInt, String]): Unit = ()

  case class Wrapper[K, V](
    @extern
    theMap: TrieMap[K, V]
  ) {
    @extern @pure
    def getMap: TrieMap[K, V] = theMap

    @extern
    def setMap(map: TrieMap[K, V]): Unit = ()
  }

  def prop2 = {
    val wrapper = Wrapper(getTrieMap(1))
    wrapper.setMap(wrapper.getMap)
    assert(wrapper.getMap == getTrieMap(1)) // invalid
  }
}
