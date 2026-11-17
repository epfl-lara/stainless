import stainless.annotation.*
import stainless.lang.*

object i1684a:

  trait Hashable[K]:
    @pure
    def hash(k: K): Long

  case class MemoKey(i: BigInt, j: BigInt)

  case object MemoHashable extends Hashable[MemoKey]:
    def hash(x: MemoKey): Long = 1L

  case class HashMap[K, V](hashF: Hashable[K], default: K => V):
    def apply(k: K): V =
      if hashF.hash(k) == 0L then default(k)
      else default(k)

  @opaque
  @inlineOnce
  def lemmaLookup[K, V](hm: HashMap[K, V], k: K, p: ((K, V)) => Boolean): Unit = {
    require(p((k, hm(k))))
    ()
  }.ensuring(_ => p((k, hm(k))))

  def lemmaMemo(memo: HashMap[MemoKey, BigInt], i: BigInt, j: BigInt): Unit = {
    require(memo(MemoKey(i, j)) == 0)
    val key: MemoKey = MemoKey(i, j)
    lemmaLookup[MemoKey, BigInt](memo, key, p => p._2 == 0)
  }.ensuring(_ => memo(MemoKey(i, j)) == 0)
