import stainless.lang._
import stainless.collection._

object FunnyScalacInference {

  sealed trait Color
  case class Red() extends Color
  case class Green() extends Color
  case class Blue() extends Color

  def product1(b: Boolean) = {
    if (b) Red()
    else Green()
  }

  def product2(b: Boolean) = {
    val x = if (b) Red() else if (b && b) Red() else Green()
    ()
  }

  def product3(c: Color) = {
    val x = c match {
      case Red() => Red()
      case Green() => Red()
      case Blue() => Blue()
    }
    x
  }

  def product4(c: Color) = {
    val x = c match {
      case Red() => Red()
      case Green() => Red()
      case Blue() => Blue()
    }
    List(x)
  }

  def product5(c: Color) = {
    val x = c match {
      case Red() => List(Red())
      case Green() => List(Red())
      case Blue() => List(Blue())
    }
    x
  }
}