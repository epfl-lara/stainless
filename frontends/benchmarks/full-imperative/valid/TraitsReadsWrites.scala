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

  case class IncTask() extends Task {
    def readSet: Set[AnyHeapRef] = Set[AnyHeapRef]()
    def writeSet: Set[AnyHeapRef] = Set[AnyHeapRef]()

    @opaque
    def run(): Unit = {
      reads(readSet)
      modifies(writeSet)
      ()
    }
  }  
}
