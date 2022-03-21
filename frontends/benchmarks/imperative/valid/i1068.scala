object i1068 {

  def f(x1: Int, x2: Int, x3: Int): Unit = {
    require(x1 == 1)
    require(x2 == 1)
    require(x3 == 3)
  }

  def test: Unit = {
    var x = 0
    f({x += 1; x}, x, {x+= 2; x })
  }

  case class Box(var field: Int)

  def test2(v: Box): Unit = {
    v.field = 0
    f({v.field += 1; v.field}, v.field, {v.field+= 2; v.field})
  }

}