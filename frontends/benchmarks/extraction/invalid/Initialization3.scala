object Initialization3 {
  case class NoThis() {
    val nothis: Boolean = h()

    def f(): NoThis = this
    def h(): Boolean = f().nothis
  }
}
