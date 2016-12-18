object PatternGuards1 {

  def test(y: Int): Int = {
    var x = y
    def foo(): Boolean = x > 10

    x = x + 1
    
    x match {
      case z if x > 11 => z
      case _ => 12
    }
  } ensuring(_ > 11)

}
