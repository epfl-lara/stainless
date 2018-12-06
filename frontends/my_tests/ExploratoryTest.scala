//import stainless.lang.Bag

object ExploratoryTest {


  def foo(baz: (Int, (Int, Boolean))): String = baz match {
    case b @ (2, (1, true)) => "Stevan"
    case a @ (1, (2, false)) => "Romain"
  }
}