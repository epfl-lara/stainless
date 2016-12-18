object NestedFunState8 {
  
  def test() = {
    var local = 0
    def foo(a: Int): Boolean = { local == a }

    local += 1
    assert(foo(1))
  }

}
