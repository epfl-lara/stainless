import stainless.annotation._

trait NonMutableTypeParameters[X,Y]
trait MutableTypeParameter[@mutable X] extends NonMutableTypeParameters[X, X] {
  def f() = ()
}
