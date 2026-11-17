object MemberClassesUnsupported {

  trait Generic[T] {
    case class Inner(t: T)
  }

  trait WithObject {
    object Inner
  }

  case object Obj {
    case class InCaseObject()
  }

  // Case classes compare structurally, while outer instances are compared by reference
  case class CaseOuter() {
    case class CaseInner()
  }

  def local: BigInt = {
    case class Local() {
      case class InLocal()
    }
    0
  }

}
