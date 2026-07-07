import stainless.lang._
import stainless.annotation._

object SoundInvariants {

  case class Valid1(x: Int) {
    require(x > 0)
  }

  case class Invalid1(y: Int) {
    require(double > 0)
    def double = y + y
  }

  def testV(v: Valid2) = true
  case class Valid2(sub: Option[Valid2]) {
    require(sub.forall(testV))
  }

  def testI(v: Invalid2) = true
  case class Invalid2(sub: Option[Valid2]) {
    require(testI(this))
  }

  def isValid(x: VADT): Boolean = x match {
    case VEmp() => false
    case VSub(s) => isValid(s)
  }

  sealed abstract class VADT {
    require(this match {
      case VEmp() => false
      case VSub(sub) => isValid(sub)
    })
  }
  case class VEmp() extends VADT
  case class VSub(x: VADT) extends VADT

  def isValid2(x: IADT) = {
    x != IEmp(0)
  }

  sealed abstract class IADT {
    require(this match {
      case that @ _ => isValid2(that)
    })
  }
  case class IEmp(a: Int) extends IADT

  sealed abstract class Abs {
    require(x != 0)
    val x: Int
    val y: Int
    def z: Int
  }
  case class AbsValid(x: Int, y: Int, z: Int) extends Abs

}

