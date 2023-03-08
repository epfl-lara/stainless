object defs {
  sealed trait OpKind
  object OpKind {
    case object Add extends OpKind
    case object Sub extends OpKind
    case object Mul extends OpKind
  }
}