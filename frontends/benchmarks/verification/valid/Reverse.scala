import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof._

object Reverse {
  sealed abstract class IList
  case class ICons(head: BigInt, tail: IList) extends IList
  case class INil() extends IList


  def reverse0(l1: IList, l2: IList): IList = (l1 match {
    case INil()       => l2
    case ICons(x, xs) => reverse0(xs, ICons(x, l2))
  })

  def content(l: IList): Set[BigInt] = l match {
    case INil()       => Set.empty[BigInt]
    case ICons(x, xs) => Set(x) ++ content(xs)
  }
  
  @traceInduct("reverse0")
  def revPreservesContent(l1: IList, l2: IList): Boolean = {
    content(l1) ++ content(l2) == content(reverse0(l1, l2))
  }.holds
}

