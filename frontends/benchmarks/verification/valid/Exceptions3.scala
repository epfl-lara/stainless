import stainless.lang._
case class Bad(x: BigInt) extends Exception
// Methods may throw, and their overrides too
abstract class Shape {
  def area(k: BigInt): BigInt = {
    require(k >= 0)
    AbstractMethodBody[BigInt]()
  }.ensuring(_ >= 0).throwing { case Bad(x) => x < 0; case _ => false }
}
case class Square(s: BigInt) extends Shape {
  override def area(k: BigInt): BigInt = {
    require(k >= 0)
    if (s < 0) throw Bad(s)
    s * s * k
  }.ensuring(_ >= 0).throwing { case Bad(x) => x < 0; case _ => false }
}
object Exceptions3 {
  def total(sh: Shape): BigInt = {
    try sh.area(1) catch { case Bad(_) => BigInt(0) }
  }.ensuring(_ >= 0)
}
