//import stainless.lang.Bag

object ExploratoryTest {


  def foo(baz: (Int, Int)): Int = baz match {
    case a @ (1, 2) => a._2
    case (b @ 2, c @ 3) => c
  }
}