import stainless.lang._
import stainless.collection._
import stainless.annotation._

object HashMapResize {
  @extern
  def hash[K](k: K): BigInt = {
    (??? : BigInt)
  }.ensuring(res => res >= 0)

  case class FixedSizeMap[K, V](buckets: MutableMap[BigInt, List[(K, V)]], size: BigInt) {
    require(size > 0)

    def index(k: K): BigInt = {
      hash(k) % size
    }.ensuring(res => 0 <= res && res < size)

    def insert(k: K, v: V): Unit = {
      val i = index(k)
      buckets(i) = (k, v) :: buckets(i).filter(_._1 != k)
    }.ensuring(_ => size == old(this).size)

    def insertAll(l: List[(K, V)]): Unit = {
      decreases(l)
      l match {
        case Nil() => ()
        case Cons((k, v), t) =>
          insert(k, v)
          insertAll(t)
      }
    }.ensuring(_ => size == old(this).size)
  }

  case class HashMap[K, V](var inner: FixedSizeMap[K, V]) {
    def resize(newSize: BigInt): Unit = {
      require(newSize > 0)

      val newMap = FixedSizeMap[K, V](MutableMap.withDefaultValue[BigInt, List[(K, V)]](() => Nil()), newSize)
      var i = BigInt(0)

      (while (i < inner.size) {
        decreases(inner.size - i)
        newMap.insertAll(inner.buckets(i))
        i += 1
      }).invariant(newMap.size == newSize)
      inner = newMap
    }.ensuring(_ => inner.size == newSize)
  }

  def f[K, V](h: HashMap[K, V], k: K, v: V): Unit = {
    require(h.inner.size == 4)

    val prev = h.inner

    h.resize(8)
    prev.insert(k, v)

    assert(prev.size == 4)
    assert(h.inner.size == 8)
  }
}
