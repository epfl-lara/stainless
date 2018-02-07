object Zeros2 {
  case class SCons(x: BigInt, tail: () => SCons)
  def looping(): SCons = SCons(0, () => looping().tail())
}
