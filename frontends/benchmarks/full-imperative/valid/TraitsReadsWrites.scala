import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.Option._
import stainless.lang.StaticChecks._
import stainless.proof.check

object TraitsReadsWrites {
  @mutable abstract class Task {  
    def readSet: Set[AnyHeapRef]
    def writeSet: Set[AnyHeapRef]

    def run(): Unit = {
      require(writeSet.subsetOf(readSet))
      reads(readSet)
      modifies(writeSet)
      ??? : Unit
    }
  }

  case class NothingTask() extends Task {
    def readSet: Set[AnyHeapRef] = Set[AnyHeapRef]()
    def writeSet: Set[AnyHeapRef] = Set[AnyHeapRef]()

    @opaque
    override def run(): Unit = {
      reads(readSet)
      modifies(writeSet)
      ()
    }
  }

  case class IntBox(var value: BigInt) extends AnyHeapRef
  
  case class IncTask(box: IntBox) extends Task {
    def readSet: Set[AnyHeapRef] = Set[AnyHeapRef](box)
    def writeSet: Set[AnyHeapRef] = Set[AnyHeapRef](box)

    @opaque
    override def run(): Unit = {
      reads(readSet)
      modifies(writeSet)
      box.value = box.value + 1
    }
  }
  
}
