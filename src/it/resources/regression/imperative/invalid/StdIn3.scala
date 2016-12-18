import stainless.io._

object StdIn3 {

  //should be invalid because of MinInt
  def abs: Int = {
    implicit val state = stainless.io.newState
    val n = StdIn.readInt
    if(n < 0) -n else n
  } ensuring(_ >= 0)

}
