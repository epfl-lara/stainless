import leon.collection._

object ADTWithArray2 {

  case class B(content: Array[List[BigInt]]) {
    require(content.length > 0 && content.length < 100)

    def contains(y: BigInt): Boolean = {
      y >= 0
    } ensuring(res => res == content(0).contains(y))
  }

}
