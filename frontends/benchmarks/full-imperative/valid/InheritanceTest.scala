import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

object SimpleInheritanceTest {
  abstract class Task {
    def region: Set[AnyHeapRef]
    
    def run: BigInt = {
      reads(region)
      modifies(region)
      42
    }
    
  }

  case object pureTask extends Task {
    def region = Set[AnyHeapRef]()
    def run = {
      42
    }
  }
  
  @inline
  def disjoint(t1: Task, t2: Task): Boolean = {
      (t1.region & t2.region) == Set[AnyHeapRef]()
  }

  def parallel(t1: Task, t2: Task): (BigInt, BigInt) = {
    require(disjoint(t1, t2))
    reads(t1.region ++ t2.region)
    modifies(t1.region ++ t2.region)
    (t1.run, t2.run)
  }
  @extern
  def main(args: Array[String]): Unit = {
  }
}
