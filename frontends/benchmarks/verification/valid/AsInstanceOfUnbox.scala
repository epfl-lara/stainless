package asInstanceOfUnbox

def test: Boolean =
  val x: Any = true
  x.asInstanceOf[Boolean]
