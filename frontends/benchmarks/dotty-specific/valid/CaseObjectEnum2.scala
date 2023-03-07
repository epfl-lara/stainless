object CaseObjectEnum2 {
  object Nest {
    enum OpKind {
      case Add
      case Sub
      case Mul
    }
  }

  def eval1(x: BigInt, y: BigInt, kind: Nest.OpKind) = kind match {
    case Nest.OpKind.Add => x + y
    case Nest.OpKind.Sub => x - y
    case Nest.OpKind.Mul => x * y
  }

  def eval2(x: BigInt, y: BigInt, kind: Nest.OpKind) = {
    import Nest._
    kind match {
      case OpKind.Add => x + y
      case OpKind.Sub => x - y
      case OpKind.Mul => x * y
    }
  }

  def eval3(x: BigInt, y: BigInt, kind: Nest.OpKind) = {
    import Nest.OpKind._
    kind match {
      case Add => x + y
      case Sub => x - y
      case Mul => x * y
    }
  }
}