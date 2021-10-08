/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

trait VerificationAnalysis extends AbstractAnalysis {
  val program: StainlessProgram
  val context: inox.Context
  import context.given
  import program._

  val sources: Set[Identifier] // set of functions that were considered for the analysis
  val results: Map[VC[trees.type], VCResult[Model]]

  lazy val vrs: Seq[(VC[trees.type], VCResult[Model])] =
    results.toSeq.sortBy { case (vc, _) => (vc.fid.name, vc.kind.toString) }

  private lazy val records = vrs map { case (vc, vr) =>
    val time = vr.time.getOrElse(0L) // TODO make time mandatory (?)
    val status = VerificationReport.Status(program)(vr.status)
    val solverName = vr.solver map { _.name }
    val source = symbols.getFunction(vc.fid).source
    VerificationReport.Record(vc.fid, vc.getPos, time, status, solverName, vc.kind.name, derivedFrom = source)
  }

  override val name = VerificationComponent.name

  override type Report = VerificationReport

  override def toReport = new VerificationReport(records, sources)

}
