import stainless.collection._

object PostFailure {

  case class PostBox(letters: List[Letter])
  case class Letter(from: String, msg: String, to: String)

  def put(pb: PostBox, l: Letter): PostBox = {
    pb
 }.ensuring(_ == l :: pb.letters) // oh no, post fails :(

  def ohno: PostBox = put(
    PostBox(Nil()),
    Letter("Someone", ":)", "EPFL IC IINFCOM LARA")
  )
}
