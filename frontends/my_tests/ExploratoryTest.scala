//import stainless.lang.Bag

object ExploratoryTest {


  def foo(baz: Int) = baz match {
    case a @ 1 => "Romain"
    case b @ List(c: Int, d) => "Nicolas"
    case a @ (Int, String) => "Test"
    case (a, b) => "foooo"
    case _ => "Bla bla"
  }
}