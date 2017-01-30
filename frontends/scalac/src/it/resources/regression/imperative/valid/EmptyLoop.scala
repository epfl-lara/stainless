
object EmptyLoop {
  def foo = {
    val EOF = 0
    val x = 1
    while (x != EOF) { } // forever
  }
}
