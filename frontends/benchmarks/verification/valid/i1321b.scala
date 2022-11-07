object i1321b {
  trait MyInt {
    def x: BigInt
  }
  final case class PosInt(v: BigInt) extends MyInt {
    def x = v
  }

  def onlyPos(x: PosInt): PosInt =
    PosInt(x.v + 1)

  def forget[A](f: A => A): Unit = ()

  def work() = forget[PosInt](xyz => onlyPos(xyz))
}