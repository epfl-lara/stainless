
object ImportStatements {

  def prop1 = {
    import stainless.lang._
    assert(true)
  }

  def prop2 = {
    import stainless.lang._
  }

  def prop3 = {
    val x = 12
    import stainless.lang._
    assert(true)
  }

  def prop4 = {
    assert(true)
    import stainless.lang._
  }

}
