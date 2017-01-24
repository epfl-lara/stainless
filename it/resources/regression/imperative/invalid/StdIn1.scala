import stainless.io._

object StdIn1 {

  def alwaysPos: Int = {
    implicit val state = stainless.io.newState
    StdIn.readInt
  } ensuring(_ >= 0)

}
