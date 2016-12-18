object HigherOrderFunctionMutableParams17 {

  //this used to create a bug because we are passing a literal
  //array as a reference to f. It's valid, but the implementation
  //used to assume that only identifier could be passed

  case class A(var x: Int)

  def test(f: (A) => Int): Int = {
    f(A(0))
  } ensuring(res => true)

}
