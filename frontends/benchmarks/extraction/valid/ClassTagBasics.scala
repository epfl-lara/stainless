import scala.reflect.ClassTag

/** Tests that Stainless accepts `ClassTag` parameters. It should strip them
  * from the extracted code, as they are not needed for verification.
  */
object ClassTagBasics {
  def id[T: ClassTag](x: T): T = x

  def Test = id(42)
}
