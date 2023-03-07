object CaseObject4 {
  sealed trait OpKind
  object OpKind {
    case object Add extends OpKind
    case object Sub extends OpKind
    case object Mul extends OpKind
  }

  def eval1(x: BigInt, y: BigInt, kind: OpKind) = kind match {
    case OpKind.Add => x + y
    case OpKind.Sub => x - y
    case OpKind.Mul => x * y
  }
}