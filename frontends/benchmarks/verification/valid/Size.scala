import stainless.lang._
import stainless.annotation._
import stainless.proof._

object Size {
  sealed abstract class IList
  case class ICons(head: BigInt, tail: IList) extends IList
  case class INil() extends IList

  def size(l: IList): BigInt = (l match {
    case INil() => BigInt(0)
    case ICons(_, t) => 1 + size(t)
  }) //ensuring(res => res >= 0)

  @traceInduct("")
  def nonNegSize(l: IList): Unit = {
    ()
  } ensuring (size(l) >= 0)
}

