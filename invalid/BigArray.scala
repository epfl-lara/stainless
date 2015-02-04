import leon.annotation._
import leon.lang._

object BigArray {

  def big(a: Array[Int]): Int = {
    require(a.length >= 10 && a(7) == 42)
    a.length
  } ensuring(_ <= 1000000000)

}
