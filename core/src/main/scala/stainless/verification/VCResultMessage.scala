/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

case class VCResultMessage[T <: ast.Trees, +M](
  vc: VC[T],
  result: VCResult[M]
) extends ReportMessage {

  override val sbtPluginOnly: Boolean = true

  override def toString: String = {
    s"VC '${vc.kind}' @ ${vc.getPos}: " +
    s"${result.status.name.toUpperCase}"
  }

  override def emit(reporter: inox.Reporter): Unit = {
    result.status match {
      case VCStatus.Valid =>
        reporter.warning(vc.getPos, toString)

      case VCStatus.Invalid(reason) =>
        reporter.error(vc.getPos, toString)

        reason match {
          case VCStatus.CounterExample(cex) =>
            reporter.error(vc.getPos, "Found counter-example:")
            reporter.error(vc.getPos, "  " + cex.toString.replaceAll("\n", "\n  "))

          case VCStatus.Unsatisfiable =>
            reporter.error(vc.getPos, "Property wasn't satisfiable")
        }

      case status =>
        reporter.error(vc.getPos, toString)
        reporter.error(vc.getPos, " => " + result.status.name.toUpperCase)
    }
  }
}
