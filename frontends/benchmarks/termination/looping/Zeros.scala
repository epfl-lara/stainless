object Zeros {
  abstract class Stream
  case class SCons(head: BigInt, tail: () => Stream) extends Stream

  def tail(s: Stream): Stream = s match {
    case SCons(_, tail) => tail()
  }

  def looping_zeros(): Stream = tail(SCons(0, looping_zeros()))

  val looing_x = looping_zeros() // reduces to tail(SCons(0, looping_zeros _)), i.e. looping_zeros() (loop)
}
