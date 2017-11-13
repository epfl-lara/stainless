import stainless.collection._
import stainless.lang._

object Extraction1 {

  def wrongTheorem[A](l: List[A], x: A): Boolean = {
    l.content == l.content - x
  }.holds

}
