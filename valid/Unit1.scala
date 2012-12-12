object Unit1 {

  def foo(): Unit = ({
    ()
  }) ensuring(_ == ())

}
