object StaticDefaultGetter {

  def foo(x: Boolean = true): Boolean = x

  def bar(): Unit = {
    require(foo())
    ()
  }
}
