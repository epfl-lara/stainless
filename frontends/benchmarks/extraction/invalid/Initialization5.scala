object Initialization5 {
  case class NoThis() {
    val nothis1 = f()
    val nothis2 = 0

    def f() = g(this)
    def g(nt: NoThis) = nt.nothis2

  }
}
