object i1349b {
  final case class Wrap[A](a: A) {
    def get: A = a
  }

  type WInt = Wrap[Int]

  case class IndexedKey(key: WInt) {
    require(key.get < 100)
  }

  def mkIndexedKey1(key: WInt): IndexedKey = {
    require(key.get < 100)
    IndexedKey(key)
  }

  def mkIndexedKey2(key: Wrap[Int]): IndexedKey = {
    require(key.get < 100)
    IndexedKey(key)
  }
}