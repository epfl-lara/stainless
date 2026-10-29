import stainless.annotation._

// An exported constant is defined in the header file, so the function it refers to must be exported too.
object ConstantExportedFunction {

  def incImpl(x: Int): Int = x + 1

  @cCode.`export`
  val Inc: Int => Int = (x: Int) => incImpl(x)

}
