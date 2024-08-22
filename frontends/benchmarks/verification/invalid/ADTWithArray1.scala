object ADTWithArray1 {

  case class A(x: Int)

  case class B(content: Array[A]) {
    require(content.length > 0)

    def contains(y: Int): Boolean = {
      require(content.length > 0)
      content(0).x == y
    }.ensuring(res => res)
  }

}
