abstract class High[A] {
  def zero: A // works if commented
}

abstract class Mid[A] extends High[A] {
  def one: A
}

case class Low() extends Mid[BigInt] {
  override def zero: BigInt = 0 // works if commented
  override def one: BigInt = 1
}
