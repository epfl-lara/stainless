import language.experimental.qualifiedTypes.silent
import stainless.annotation.ghost
import stainless.lang._
import stainless.lang.StaticChecks._

case class A(@ghost val x: BigInt) {

  def f(v: BigInt): Boolean = {
    require(v >= x)
    // The following refinement type should not be allowed to access ghost symbols, as its predicate is executed at runtime.
    if(v.isInstanceOf[{i: BigInt with i >= x}]) then true else false
  }
}