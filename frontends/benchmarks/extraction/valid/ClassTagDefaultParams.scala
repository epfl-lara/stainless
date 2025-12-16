import scala.reflect.ClassTag

/** Tests that Stainless accepts `ClassTag` parameters. It should strip them
  * from the extracted code, as they are not needed for verification.
  */
object ClassTagDefaultParams {
  def f(c: ClassTag[Int] = ClassTag.Int): Int = 42
}
