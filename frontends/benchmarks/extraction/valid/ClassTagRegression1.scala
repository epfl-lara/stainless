import scala.reflect.ClassTag

/** Tests that Stainless accepts `ClassTag` parameters. It should strip them
  * from the extracted code, as they are not needed for verification.
  */
object ClassTagRegression1 {

  case class Cache1[C: ClassTag](v: C):
    def get: C = v
  case class Cache2[C: ClassTag](v: C):
    def get: C = v

  def f[C: ClassTag](v: C, v2: C)(using cache1: Cache1[C], cache2: Cache2[C]): C = {
    g[C](v)
  }

  def g[C: ClassTag](v: C)(using cache1: Cache1[C], cache2: Cache2[C]): C = {
    cache1.get
  }
  

  @main def ClassTagRegression1() = 
    val c1 = Cache1[Int](10)
    val c2 = Cache2[Int](20)
    val c = f[Int](42, 84)(using ClassTag.Int, c1, c2)
    assert(c == 10)
}
