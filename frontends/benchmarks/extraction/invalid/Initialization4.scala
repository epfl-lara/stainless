object Initialization4 {
  case class NoThis() {
    val nothis = f()
    val g = 1

    def f() = this.g
  }
}
