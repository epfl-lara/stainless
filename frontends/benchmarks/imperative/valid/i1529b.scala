import stainless.lang.*

object i1529b {
  case class Key(i: BigInt)
  case class Value(i: BigInt)
  type MutableMapAlias = MutableMap[Key, Value]

  case class MutableMapWrapper(mm: MutableMapAlias)

  def test(mmw: MutableMapWrapper): Unit = {
    require(mmw.mm(Key(42)) == Value(24))
    mmw.mm(Key(2)) = Value(4)
    val mmw2 = MutableMapWrapper(MutableMap.withDefaultValue(() => Value(123)))
    assert(mmw2.mm(Key(1)) == Value(123))
  }
}