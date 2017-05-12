import stainless.lang._

object ExpressionOrder2 {

  def testArrayAccess() = {
    val a = Array(0, 1, 2, 3)
    val b = Array(9, 9, 9)
    var c = 666
    val i = 9
    val x = (if (i != 9) b else { c = 0; a })(if (i == 9) { c = c + 1; 0 } else 1)

    x == 0 && c == 1
  }.holds

}
