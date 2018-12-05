//import stainless.lang.Bag

object ExploratoryTest {


  def foo(baz: BigInt) = baz match {
    case a @ 1 => "Romain"
    case b @ 2 => "Stevan"
  }
}