object PatternGuards2 {

  def test(y: Int): Int = {
    var x = y
    def foo(): Boolean = x > 10

    x = x + 1
    
    x match {
      case z if foo() => x
      case _ => 11
    }
  } ensuring(_ > 10)

}
