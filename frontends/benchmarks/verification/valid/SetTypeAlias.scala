import stainless.lang.*

object SetTypeAlias {
  type SetAlias = Set[Byte]

  case class SetAliasWrapper(sa: SetAlias)

  def test(saw: SetAliasWrapper, six: SetAliasWrapper): Unit = {
    require(saw.sa.contains(42))
    val saucisse = saw.sa ++ six.sa
    assert(saucisse.contains(42))
  }
}