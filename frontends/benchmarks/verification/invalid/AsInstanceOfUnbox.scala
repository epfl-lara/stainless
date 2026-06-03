package asInstanceOfUnbox

def test: Boolean =
  val x: Any = 1
  x.asInstanceOf[Boolean]
