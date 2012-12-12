object Unit1 {

  def foo(u: Unit): Unit = ({
    u
  }) ensuring(_ != ())

}
