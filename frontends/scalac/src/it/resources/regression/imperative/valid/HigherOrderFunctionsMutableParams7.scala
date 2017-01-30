object HigherOrderFunctionsMutableParams7 {
  /*
   * this test catches an error that happened in
   * imperative when renaming higher order functions parameter
   * even though the function had a pure signature (Int => Int)
   */

  def app(f: (Int) => Int, x: Int): Int = {
    f(x)
  }

  def id(x: Int) = x

  def test(): Int = {
    val x = 12
    app(id, 12)
  } ensuring(_ == 12)

}
