object CaseObjectEnum1 {
  enum OpKind {
    case Add
    case Sub
    case Mul
  }

  def eval1(x: BigInt, y: BigInt, kind: OpKind) = kind match {
    case OpKind.Add => x + y
    case OpKind.Sub => x - y
    case OpKind.Mul => x * y
  }

  def eval2(x: BigInt, y: BigInt, kind: OpKind) = {
    import OpKind._
    kind match {
      case Add => x + y
      case Sub => x - y
      case Mul => x * y
    }
  }
}