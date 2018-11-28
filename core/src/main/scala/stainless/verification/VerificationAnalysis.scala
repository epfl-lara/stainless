/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

trait VerificationAnalysis extends AbstractAnalysis {
  val program: StainlessProgram
  implicit val context: inox.Context
  import program._

  val sources: Set[Identifier] // set of functions that were considered for the analysis
  val results: Map[VC[trees.type], VCResult[Model]]

  lazy val vrs: Seq[(VC[trees.type], VCResult[Model])] =
    results.toSeq.sortBy { case (vc, _) => (vc.fd.name, vc.kind.toString) }

  private lazy val records = vrs map { case (vc, vr) =>
    val time = vr.time.getOrElse(0L) // TODO make time mandatory (?)
    val status = VerificationReport.Status(program)(vr.status)
    val solverName = vr.solver map { _.name }
    val source = symbols.getFunction(vc.fd).source
    VerificationReport.Record(vc.fd, vc.getPos, time, status, solverName, vc.kind.name, derivedFrom = source)
  }

  override val name = VerificationComponent.name

  override type Report = VerificationReport

  override def toReport = new VerificationReport(records, sources)

}
