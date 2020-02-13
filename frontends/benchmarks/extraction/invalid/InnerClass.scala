
object InnerClass {

  trait TraitOuter {
    case class TraitInner()
  }

  abstract class ClassOuter {
    case class ClassInner()
  }

  case class CaseOuter() {
    case class CaseInner()
  }

}
