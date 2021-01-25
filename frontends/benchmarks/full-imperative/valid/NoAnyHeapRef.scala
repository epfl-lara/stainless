import stainless.collection._
import stainless.lang._

// Should work with --full-imperative even though we don't mention AnyHeapRef
object StainlessIssueFI {
  def foo[T](l: List[T]): Unit = {
    ()
  }
}
