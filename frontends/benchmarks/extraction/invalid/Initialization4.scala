object Initialization4 {
  case class NoThis() {
    val nothis = f()

    def f() = this
  }
}
