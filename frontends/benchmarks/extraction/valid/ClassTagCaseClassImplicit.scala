import scala.reflect.ClassTag

/** Tests that Stainless accepts `ClassTag` parameters. It should strip them
  * from the extracted code, as they are not needed for verification.
  */
object ClassTagCaseClassImplicit {
  case class Datastructure[T: ClassTag](size: Int, default: T) {
    val a = 0
    require(size > 0)
    def f(): T = 
      val data: Array[T] = Array.fill[T](size)(default)
      data(0)
  }

  @main def mainClassTagCaseClassImplicit() = 
    val c = Datastructure[Int](10, 42)
    val c1 = Datastructure[Int](10, 42)
    assert(c1.f() == c.f())
}
