object ImpureLazy2 {
  def f(): Int = {
    var counter = 0
    lazy val x = {
      counter = counter + 1
      counter
    }
    counter + x + x
  } ensuring (_ == 2)
}
