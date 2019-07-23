
object CaseObjectSuper {

  abstract class SomeSuperClass {
    def anInteger: Int = 40
  }

  case object SomeCaseObject extends SomeSuperClass {
    override def anInteger: Int = super.anInteger + 2
  }

  def someTest = {
    assert(SomeCaseObject.anInteger == 42)
  }

}
