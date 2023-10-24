@ignore
case class Cell[@mutable T](var v: T) {
    @ignore @library
    def swap(other: Cell[T]): Unit = {
    val t = other.v
    other.v = v
    this.v = t
  }
}

