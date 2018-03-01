package test

object Top {
  "abcdef" // not allowed here

  def bar(x: Int): Unit = ()

  bar(42) // not allwed here
}
