
object InnerClass {

  trait TraitOuter {
    case class TraitInner()
  }

  abstract class ClassOuter {
    case class ClassInner()
  }

  class PlainOuter {
    case class PlainInner()
  }

}
