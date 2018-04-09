abstract class CaseObjectA
case object CaseObjectC extends CaseObjectA

object CaseObjectMain {
  def f(): CaseObjectA = CaseObjectC
}
