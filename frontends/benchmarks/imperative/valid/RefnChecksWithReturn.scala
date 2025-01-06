import stainless.lang._

object RefnChecksWithReturn {

  def fun0(x: BigInt, arr: Array[BigInt]): Option[BigInt] = {
    require(arr.length >= 10)
    if (x <= 0){
      return Some(x)
    }
    arr(0) = 0
    Some(x)
 }.ensuring {
    case Some(xx) => (xx == x) && ((x > 0) ==> (arr(0) == 0))
  }

  def fun1(x: BigInt): (BigInt, Option[BigInt]) = {
    (x, (return (x + 1, Some(x))) : (BigInt, Option[BigInt]))._2
 }.ensuring {
    case (xx, Some(xx2)) => xx == x + 1 && xx2 == x
  }

  def fun2(x: BigInt): (BigInt, Option[BigInt]) = {
    (x, if (x == 0) return (x + 1, Some(x + 1)) else (x + 2, Some(x + 2)))._2
 }.ensuring {
    case (xx, Some(xx2)) =>
      val delta = if (x == 0) BigInt(1) else BigInt(2)
      xx == x + delta && xx2 == x + delta
  }

  def fun3(x: BigInt): (BigInt, Option[BigInt]) = {
    smth(0, if (x <= 0) return (0, Some(x)) else Some(0))
    (x, Some(x))
 }.ensuring {
    case (xx, Some(xx2)) =>
      if (x <= 0) xx == 0 && xx2 == x
      else xx == x && xx2 == x
  }
  def smth(x: BigInt, tpl: Option[BigInt]): Unit = ()
}
