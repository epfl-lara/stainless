import stainless.annotation._

@mutable
trait MutableTypeParameters[@mutable X,Y]
trait NonMutableTypeParameter[X] extends MutableTypeParameters[X, X] {
  def f() = ()
}
