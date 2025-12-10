import scala.reflect.ClassTag

/** Tests that Stainless accepts `ClassTag` parameters. It should strip them
  * from the extracted code, as they are not needed for verification.
  */
object ClassTagInnerArray {
  case class Datastructure[T: ClassTag](size: Int, default: T) {
    val a = 0
    require(size > 0)
    def f(): T = 
      val data: Array[T] = Array.fill[T](size)(default)
      data(0)

  }

  @main def main() = 
    val c = Datastructure[Int](10, 42)
    val c1 = Datastructure[Int](10, 42)
    assert(c1.f() == c.f())
}