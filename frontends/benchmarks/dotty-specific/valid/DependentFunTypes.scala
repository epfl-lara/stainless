
object DependentFunTypes {

  trait Entry {
    type Key
    def key: Key
  }

  def extractKey(e: Entry): e.Key = e.key

  def extractor: (e: Entry) => e.Key = extractKey(_)

  case class IntEntry() extends Entry {
    type Key = Int
    def key: Int = 42
  }

  def test1(entry: IntEntry) = {
    assert(extractor(entry) == 42)
  }

  def test2(entry: Entry) = {
    assert(extractor(entry) == entry.key)
  }

}
