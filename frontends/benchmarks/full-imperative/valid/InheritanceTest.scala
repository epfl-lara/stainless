import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

object SimpleInheritanceTest {
  @mutable abstract class Task {
    def region: Set[AnyHeapRef]

    def run: Unit = {
      reads(region)
      modifies(region)
      ??? : Unit
    }

    def join: BigInt = {
      reads(region)
      ??? : BigInt
    }
  }

  case object pureTask extends Task {
    def region = Set[AnyHeapRef]()
    override def run = ()
    override def join = 42
  }

  case class IntBox(var value: BigInt) extends AnyHeapRef

  case class SumTask(box: IntBox) extends Task {
    def region: Set[AnyHeapRef] = Set[AnyHeapRef](box)

    override def run = {
      reads(region)
      modifies(region)
      box.value = box.value + box.value
      ()
    }

    override def join: BigInt = {
      reads(region)
      box.value
    }
  }

  @inline
  def disjoint(t1: Task, t2: Task): Boolean = {
      (t1.region & t2.region) == Set[AnyHeapRef]()
  }

  @opaque
  def parallel(t1: Task, t2: Task): (BigInt, BigInt) = {
    require(disjoint(t1, t2))
    reads(t1.region ++ t2.region)
    modifies(t1.region ++ t2.region)
    t1.run
    t2.run
    (t1.join, t2.join)
  } ensuring { res => res == (t1.join, t2.join) }
}
