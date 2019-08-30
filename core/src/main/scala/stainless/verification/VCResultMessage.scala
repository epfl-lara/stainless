/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

case class VCResultMessage[T <: ast.Trees, +M](
  vc: VC[T],
  result: VCResult[M]
) extends ReportMessage {

  override val sbtPluginOnly: Boolean = true

  def title: String = {
    s"VC '${vc.kind}' @ ${vc.getPos}: " +
    s"${result.status.name.toUpperCase}"
  }

  override def emit(reporter: inox.Reporter): Unit = {
    result.status match {
      case VCStatus.Valid =>
        reporter.warning(vc.getPos, title)

      case VCStatus.Invalid(reason) =>
        val reasonStr = reason match {
          case VCStatus.CounterExample(cex) =>
            s"Found counter-example:\n  ${cex.toString.replaceAll("\n", "\n  ")}"

          case VCStatus.Unsatisfiable =>
            "Property wasn't satisfiable"
        }

        val msg = s"$title\n$reasonStr"
        reporter.error(vc.getPos, msg)

      case status =>
        val msg = s"$title\n => ${result.status.name.toUpperCase}"
        reporter.error(vc.getPos, msg)
    }
  }
}
