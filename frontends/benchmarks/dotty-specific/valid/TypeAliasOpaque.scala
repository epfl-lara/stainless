object TypeAliasOpaque {
  object OpaqueLongWrap {
    opaque type OpaqueLong = Long
    extension (ol: OpaqueLong) {
      def toLong: Long = ol
    }
    object OpaqueLong {
      def fromLong(l: Long): OpaqueLong = l
    }
  }

  import OpaqueLongWrap.*

  type AliasedOpaqueLong = OpaqueLong
  type Tayst = Int

  def test1(x: AliasedOpaqueLong): Unit = {
    assert(OpaqueLong.fromLong(x.toLong) == x)
  }

  def test2(x: Long): Unit = {
    assert(OpaqueLong.fromLong(x).toLong == x)
  }

  def mkAliasedOpaqueLong(x: Long): AliasedOpaqueLong = OpaqueLong.fromLong(x).ensuring(res => res.toLong == x)
}