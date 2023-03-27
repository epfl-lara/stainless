import stainless.lang._
import stainless.collection._

object i1349a {
  type Index = BigInt

  type LIndex = List[Index]

  case class IndexedKey(index: BigInt, key: LIndex) {
    require(0 <= index && index < key.length)
  }

  def mkIndexedKey1(index: BigInt, key: LIndex): IndexedKey = {
    require(0 <= index && index < key.length)
    IndexedKey(index, key)
  }

  def mkIndexedKey2(index: BigInt, key: List[Index]): IndexedKey = {
    require(0 <= index && index < key.length)
    IndexedKey(index, key)
  }

  def mkIndexedKey3(index: Index, key: LIndex): IndexedKey = {
    require(0 <= index && index < key.length)
    IndexedKey(index, key)
  }
}