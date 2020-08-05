object Initialization6 {
  case class NoThis() {
    val nothis: Boolean = h()

    def f(): NoThis = this
    def h(): Boolean = f().nothis
  }
}
