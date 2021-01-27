import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.Option._
import stainless.lang.StaticChecks._
import stainless.proof.check

object TaskImpls {
  @mutable sealed abstract class Task {
    def readSet: Set[AnyHeapRef]
    def writeSet: Set[AnyHeapRef]

    def run(): Unit = {
      reads(readSet)
      modifies(writeSet)
      ??? : Unit
    }
  }

  def parallel(task1: Task, task2: Task): Unit = {
    reads(task1.readSet ++ task2.readSet)
    modifies(task1.writeSet ++ task2.writeSet)
    require(
      (task1.writeSet & task2.readSet).isEmpty &&
      (task2.writeSet & task1.readSet).isEmpty
    )
    task1.run()
    task2.run()
    // task1 and task2 join before this function returns
  }

  case class IntBox(var value: BigInt) extends AnyHeapRef

  case class IncTask(box: IntBox) extends Task {
    def readSet: Set[AnyHeapRef] = Set[AnyHeapRef](box)
    def writeSet: Set[AnyHeapRef] = Set[AnyHeapRef](box)

    def run(): Unit = {
      reads(readSet)
      modifies(writeSet)
      box.value = box.value + 1
    }
  }

  def parallelInc(box1: IntBox, box2: IntBox): Unit = {
    reads(Set(box1, box2))
    modifies(Set(box1, box2))
    require(box1 != box2)

    val v1a = box1.value
    val v2a = box2.value

    val task1 = IncTask(box1)
    val task2 = IncTask(box2)
    parallel(task1, task2)

    assert(box1.value == v1a + 1)
    assert(box2.value == v2a + 1)
  }
}
