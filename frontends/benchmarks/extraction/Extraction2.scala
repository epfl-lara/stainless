import stainless.lang._

object Extraction2 {

  def test[T](p: T => Boolean): Boolean = {
    forall (p)
  } 
}
