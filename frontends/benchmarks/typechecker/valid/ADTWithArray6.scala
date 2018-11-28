object ADTWithArray6 {

  case class A(x: Int)

  case class B(content: Array[A]) {
    require(content.length > 0)

    def update(y: Int): B = {
      B(Array(A(y)))
    } ensuring(res => res.content(0).x == y)
  }

}
