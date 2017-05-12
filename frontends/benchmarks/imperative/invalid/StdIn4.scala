import stainless.io._

object StdIn4 {

  def readBoolCanBeFalse: Boolean = {
    implicit val state = stainless.io.newState
    StdIn.readBoolean
  } ensuring(res => res)

}
