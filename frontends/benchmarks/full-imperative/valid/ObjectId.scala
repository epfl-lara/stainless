import stainless.lang._
import stainless.lang.StaticChecks._

object ObjectIdExample {
  def f(x: AnyHeapRef, y: AnyHeapRef): Unit = {
    assert((x refEq y) == (objectId(x) == objectId(y)))
  }
}
