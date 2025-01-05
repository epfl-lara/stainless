object PatternAlternative1 {
  sealed trait SignSet
  case object None extends SignSet
  case object Any extends SignSet
  case object Neg extends SignSet 
  case object Zer extends SignSet
  case object Pos extends SignSet
  case object NegZer extends SignSet
  case object  NotZer extends SignSet
  case object  PosZer extends SignSet

  def subsetOf(a: SignSet, b: SignSet): Boolean = (a, b) match {
    case (None, _) => true
    case (_, Any) => true
    case (Neg, NegZer | NotZer) => true
    case (Zer, NegZer | PosZer) => true
    case (Pos, NotZer | PosZer) => true
    case _                  => false
  }
}