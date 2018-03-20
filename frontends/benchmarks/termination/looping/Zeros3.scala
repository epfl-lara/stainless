object Zeros3 {
  case class SCons(tail: () => SCons)
  def looping(): SCons = SCons(() => SCons(() => looping().tail().tail()))
}
