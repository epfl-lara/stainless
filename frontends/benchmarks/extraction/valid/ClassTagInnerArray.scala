import scala.reflect.ClassTag

/** Tests that Stainless accepts `ClassTag` parameters. It should strip them
  * from the extracted code, as they are not needed for verification.
  */
object ClassTagInnerArray {
  case class Datastructure[T](size: Int, ct: ClassTag[T], default: T) {
    require(size > 0)
    def f(): T = 
      val data: Array[T] = Array.fill[T](size)(default)(using ct)
      data(0)

  }
}