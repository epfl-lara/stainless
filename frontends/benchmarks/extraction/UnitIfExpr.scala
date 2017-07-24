
object UnitIfExpr {

  case class Wrap[A,B](f: A => B) {
    def apply(k: A): B = {
      f(k)
    }
  }

  def untyped(f: Wrap[BigInt,BigInt]): Unit = {
    if (f(0) < 0) {
      f(0)
    }

    f(0)
  } 
}

