package isInstanceOfInt
import stainless.annotation.extern

def test: Int =
  @extern
  val x: Any = ???

  if x.isInstanceOf[Int]
  then x.asInstanceOf[Int] + 2
  else 3
