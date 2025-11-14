enum UnaryNat:
  case Zero
  case Succ(pred: UnaryNat)

  def prev: UnaryNat = this match
    case Zero     => Zero
    case Succ(n0) => n0

  def isEven1: Boolean = this match
    case Zero => true
    case Succ(pred) => pred.isOdd1

  def isOdd1: Boolean = this match
    case Zero => false 
    case Succ(pred) => pred.isEven1
      
  def isEven2: Boolean = this match
    case Zero => true
    case Succ(pred) => pred.isOdd2

  def isOdd2: Boolean = this match
    case Zero => false 
    case Succ(Zero) => true 
    case Succ(Succ(Zero)) => false 
    case _ => this.prev.isEven2
