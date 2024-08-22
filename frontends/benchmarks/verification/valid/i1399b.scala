import stainless.lang._
import stainless.collection._
import stainless.annotation._

object i1399b {

  def foo(key: Boolean): Boolean = false

  def bar(l: List[(Boolean, Unit)]): List[(Boolean, Boolean)] = l.map { case (key, keyMapping) => key -> foo(key)}

  def barEqualsItsBody(l: List[(Boolean, Unit)]): Unit = {
 }.ensuring(bar(l) == (l.map { case (key, keyMapping) => key -> foo(key)}))

}
