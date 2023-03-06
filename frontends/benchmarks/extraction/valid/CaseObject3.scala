object CaseObject3 {
  sealed trait OpKind
  case object Add extends OpKind
  case object Sub extends OpKind
  case object Mul extends OpKind

  def eval(x: BigInt, y: BigInt, kind: OpKind) = kind match {
    case Add => x + y
    case Sub => x - y
    case Mul => x * y
  }
}