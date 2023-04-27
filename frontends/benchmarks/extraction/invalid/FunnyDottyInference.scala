import stainless.lang._
import stainless.collection._

object FunnyDottyInference {
  def matchable1(b: Boolean) = {
    if (b) 1
    else "2"
  }

  def matchable2(b: Boolean) = {
    val x = if (b) 1 else if (b && b) "2" else true
    ()
  }

  enum Color {
    case Red
    case Green
    case Blue
  }
  def matchable3(c: Color) = {
    val x = c match {
      case Color.Red => 1
      case Color.Green => "green"
      case Color.Blue => true
    }
    x
  }

  def matchable4(c: Color) = {
    val x = c match {
      case Color.Red => 1
      case Color.Green => "green"
      case Color.Blue => true
    }
    List(x)
  }

  def matchable5(c: Color) = {
    val x = c match {
      case Color.Red => List(1)
      case Color.Green => List("green")
      case Color.Blue => List(true)
    }
    x
  }
}