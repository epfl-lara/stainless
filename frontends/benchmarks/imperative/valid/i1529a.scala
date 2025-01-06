object i1529a {
  type ByteArray = Array[Byte]

  case class ByteArrayWrapper(ba: ByteArray)

  def test(baw: ByteArrayWrapper): Unit = {
    require(baw.ba.length == 64)
    baw.ba(0) = 3
    val ba2 = baw.ba.updated(0, 4.toByte)
    assert(ba2(0) == 4)
  }
}