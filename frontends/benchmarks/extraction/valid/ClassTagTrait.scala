import scala.reflect.ClassTag

/** Tests that Stainless accepts `ClassTag` parameters. It should strip them
  * from the extracted code, as they are not needed for verification.
  */
object ClassTagTrait {
  trait MyTrait[T: ClassTag] {
    def getDefault: T
  }
}
