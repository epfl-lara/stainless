object Lambda1 {

  def test(): Int = {
    val x = 2
    val cl = ((y: Int) => {
      var z = y
      z = z + x
      z
    })
    cl(4)
  } ensuring(_ == 6)

}
