trait AbstractPost {
  def inv(): Boolean = (??? : Boolean)

  def f(): Unit = {
    (??? : Unit)
  } ensuring(_ => inv())
}
