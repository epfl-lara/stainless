import stainless.lang._

object any {

  def add(x: Any, s: Set[Any]): Set[Any] = {
    s + x
  }

  def e: Set[Any] = Set.empty[Any]

  def test(x: Any): Set[Any] = {
    add(x, e)
  } ensuring { _ contains x }

}

