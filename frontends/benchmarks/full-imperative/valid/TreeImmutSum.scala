/*
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.Option._
import stainless.lang.StaticChecks._
import stainless.proof.check

object TreeImmutSumExample {
  case class Cell[T](var value: T) extends AnyHeapRef

  def treeOptToSet(t: Option[Tree]): Set[AnyHeapRef] = t match {
    case None() => Set[AnyHeapRef]()
    case Some(t) => t.repr
  }

  case class Tree(
    dataCell: Cell[Option[BigInt]],
    left: Option[Tree],
    right: Option[Tree],
    repr: Set[AnyHeapRef]
  ) {
    require {
      val leftRepr = left match {
        case None() => Set[AnyHeapRef]()
        case Some(left) => left.repr
      }
      val rightRepr = right match {
        case None() => Set[AnyHeapRef]()
        case Some(right) => right.repr
      }
      repr == leftRepr ++ rightRepr ++ Set(dataCell) &&
      (leftRepr & rightRepr) == Set[AnyHeapRef]() &&
      !leftRepr.contains(dataCell) &&
      !rightRepr.contains(dataCell)
    }

    // // Leaves are considered 0-valued.
    // @inlineOnce
    // def childData(child: Option[Tree]): Option[BigInt] = {
    //   reads(treeOptToSet(child))
    //   child match {
    //     case None() => Some(0)
    //     case Some(c) => c.dataCell.value
    //   }
    // }

    // Ensur
    @inlineOnce
    def validData: Boolean = {
      reads(repr)
      val data = dataCell.value
      data.isDefined ==> {
        // val dataLeft = childData(left)
        // val dataRight = childData(right)
        val dataLeft = left match {
          case None() => Some[BigInt](0)
          case Some(c) => c.dataCell.value
        }
        val dataRight = right match {
          case None() => Some[BigInt](0)
          case Some(c) => c.dataCell.value
        }
        dataLeft.isDefined && dataRight.isDefined &&
        data.get == dataLeft.get + dataRight.get
      }
    }

    // Ensure that if data has been stored, it corresponds to the sum of the children's data.
    @opaque
    def valid: Boolean = {
      reads(repr)
      valid_impl
    }

    def valid_impl: Boolean = {
      reads(repr)
      (left.isDefined ==> left.get.valid) &&
      (right.isDefined ==> right.get.valid) &&
      validData
    }

    @extern
    def revealValid: Unit = {
      reads(repr)
      ()
   }.ensuring(_ => valid == valid_impl)

    @opaque
    def lemmaValidChildren: Unit = {
      reads(repr)
      require(valid)
      revealValid
      ()
   }.ensuring { _ =>
      (left.isDefined ==> left.get.valid) && (right.isDefined ==> right.get.valid)
    }

    @opaque
    def lemmaValidFromParts: Unit = {
      reads(repr)
      require(
        (left.isDefined ==> left.get.valid) &&
        (right.isDefined ==> right.get.valid) &&
        validData
      )
      revealValid
   }.ensuring(_ => valid)

    @opaque
    def computeSum: BigInt =  {
      reads(repr)
      modifies(repr)
      require(valid)

      dataCell.value match {
        case Some(sum) =>
          sum
        case None() =>
          // assert(left.isDefined && right.isDefined)
          lemmaValidChildren
          // assert(left.isDefined ==> left.get.valid)
          // assert(right.isDefined ==> right.get.valid)
          // assert((left.get.repr & right.get.repr).isEmpty)
          // val sum = left.get.computeSum
          // assert((left.get.repr & right.get.repr).isEmpty)
          // assert(left.get.valid)
          // assert(right.get.valid)

          val leftSum: BigInt = if (left.isDefined) left.get.computeSum else 0
          // assert(left.isDefined ==> left.get.valid)
          // assert(right.isDefined ==> right.get.valid)
          val rightSum: BigInt = if (right.isDefined) right.get.computeSum else 0
          assert(left.isDefined ==> left.get.valid)
          assert(right.isDefined ==> right.get.valid)

          assert(left.isDefined ==> !left.get.repr.contains(dataCell))
          assert(right.isDefined ==> !right.get.repr.contains(dataCell))

          val sum = leftSum + rightSum
          dataCell.value = Some(sum)

          val dataLeft = left match {
            case None() => Some[BigInt](0)
            case Some(c) => c.dataCell.value
          }
          val dataRight = right match {
            case None() => Some[BigInt](0)
            case Some(c) => c.dataCell.value
          }
          assert(dataLeft.isDefined)
          assert(dataRight.isDefined)
          assert(dataCell.value.get == dataLeft.get + dataRight.get)
          assert(validData)

          assert(left.isDefined ==> left.get.valid)
          assert(right.isDefined ==> right.get.valid)

          lemmaValidFromParts

          sum
      }
   }.ensuring(res => dataCell.value == Some(res) && valid)
  }
}
*/
