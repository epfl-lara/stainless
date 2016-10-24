import leon.lang._

object AssociativityProperties {

  def isAssociative[A](f: (A,A) => A): Boolean = {
    forall((x: A, y: A, z: A) => f(f(x, y), z) == f(x, f(y, z)))
  }

  def isCommutative[A](f: (A,A) => A): Boolean = {
    forall((x: A, y: A) => f(x, y) == f(y, x))
  }

  def isRotate[A](f: (A,A) => A): Boolean = {
    forall((x: A, y: A, z: A) => f(f(x, y), z) == f(f(y, z), x))
  }

  def assocPairs[A,B](f1: (A,A) => A, f2: (B,B) => B) = {
    require(isAssociative(f1) && isAssociative(f2))
    val fp = ((p1: (A,B), p2: (A,B)) => (f1(p1._1, p2._1), f2(p1._2, p2._2)))
    isAssociative(fp)
  }.holds

  def assocRotate[A](f: (A,A) => A): Boolean = {
    require(isCommutative(f) && isRotate(f))
    isAssociative(f)
  }.holds

  def assocRotateInt(f: (BigInt, BigInt) => BigInt): Boolean = {
    require(isCommutative(f) && isRotate(f))
    isAssociative(f)
  }.holds

}
