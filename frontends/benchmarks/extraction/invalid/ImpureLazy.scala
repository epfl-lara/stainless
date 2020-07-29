object ImpureLazy {
  def f() = {
    var x = 0
    lazy val hello = { x = x + 1 }
  }
}
