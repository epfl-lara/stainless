trait AbstractPost {
  def inv(): Boolean = stainless.lang.AbstractMethodBody[Boolean]()

  def f(): Unit = {
    stainless.lang.AbstractMethodBody[Unit]()
 }.ensuring(_ => inv())
}
