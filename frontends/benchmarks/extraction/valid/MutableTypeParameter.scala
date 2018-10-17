import stainless.annotation._

trait MutableTypeParameters[@mutable X,Y]
trait NonMutableTypeParameter[X] extends MutableTypeParameters[X, X] {
  def f() = ()
}
