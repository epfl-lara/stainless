import scala.reflect.ClassTag

/** Tests that Stainless accepts `ClassTag` parameters. It should strip them
  * from the extracted code, as they are not needed for verification.
  */
object ClassTagPatternMatch {
  case class Datastructure[T: ClassTag](size: Int, default: T) {
    require(size > 0)
    def f(): T = 
      val data: Array[T] = Array.fill[T](size)(default)
      data(0)
  }

  def patt[T: ClassTag](inst: Datastructure[T]): T = 
    inst match 
      case Datastructure(size, default) => default

  @main def mainClassTagPatternMatch() = 
    val c = Datastructure[Int](10, 42)
    val c1 = Datastructure[Int](10, 42)
    assert(patt(c1) == patt(c))
}
