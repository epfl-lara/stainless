import stainless.lang._

object StringsUTF16 {
  // Scala strings are sequences of UTF-16 code units, so a character outside of
  // the BMP counts as two, and its surrogates can be concatenated back
  def emoji: Unit = {
    assert("😀".bigLength() == 2)
    assert("a😀b".bigLength() == 4)
    assert("\ud83d" + "\ude00" == "😀")
    assert(("\ud83d" + "x").bigLength() == 2)
  }

  def single(s: String): Unit = {
    require(s.bigLength() == 1)
    assert(s != "😀")
  }
}
