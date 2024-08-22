import stainless.annotation._

object ValEnsuring {

  def f(x: Int): Int = {
    require(0 <= x && x < 100)
    val y = x * x
    require(y < 500)

    {
      y + y
   }.ensuring(res => res < 1000 && y <= res)
  }

  def g() = {
    f(20)
  }

}
