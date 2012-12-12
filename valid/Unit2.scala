object Unit2 {

  def foo(u: Unit): Unit = {
    u
  } ensuring(_ == ())

}
