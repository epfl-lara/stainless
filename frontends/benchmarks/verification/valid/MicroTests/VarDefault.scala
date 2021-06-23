object VarDefault {
  case class AA(var x: Int = 555, y: Int = 222)

  def ff() = {
    val a = AA()
    assert(a.x == 555)
    assert(a.y == 222)
    a.x = 100
    assert(a.x == 100)
    assert(a.y == 222)
  }

}
