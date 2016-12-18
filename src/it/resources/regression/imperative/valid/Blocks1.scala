object Blocks1 {

  //this used to crash as we would simplify away the final Unit, and get a typing
  //error during the solving part
  def test(a: BigInt): Unit = {
    42
    ()
  } ensuring(_ => a == (a + a - a))

}
