import scala.reflect.ClassTag

/** Tests that Stainless accepts `ClassTag` parameters. It should strip them
  * from the extracted code, as they are not needed for verification.
  */
object ClassTagBasics {
  def id[T: ClassTag](x: T): T = x
  def id2[T](x: T)(using ev: ClassTag[T]): T = x
  def id3[T](x: T)(ev: ClassTag[T]): T = x
  def id4[T](x: T, ev: ClassTag[T]): T = x

  def Test =
    id(42)
    id(42)(using ClassTag.Int)
    id2(42)
    id2(42)(using ClassTag.Int)
    id3(42)(ClassTag.Int)
    id4(42, ClassTag.Int)
}
