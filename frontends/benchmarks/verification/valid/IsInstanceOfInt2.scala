package isInstanceOfInt2

def test(x: Int): Int =
  if x.isInstanceOf[Int] then x + 0
  else 3
