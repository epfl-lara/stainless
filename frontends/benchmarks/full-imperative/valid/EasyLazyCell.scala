import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.proof._
import stainless.lang.StaticChecks._

object EasyLazyCell {
  final case class Ref[T](var unref: T) extends AnyHeapRef {
    def apply(): T = {
      reads(Set(this))
      unref
    }
  }

  final case class Lazy[T](computation : Unit => T, var value: Option[T]) extends AnyHeapRef
  {
    def apply(): T = {
      reads(Set(this))
      modifies(Set(this))
      value match {
        case Some(v) => v
        case None() => {
          val v = computation(())
          value = Some(v)
          v
        }
      }
    }
  }
  
  @extern
  def main(args: Array[String]): Unit = {
    val v1 = Lazy[BigInt](((u:Unit) => {println("Hello before!"); BigInt(42)}),
                          None[BigInt]())
    println("First me!")
    println(v1() + v1() + v1())
  }
  
}
