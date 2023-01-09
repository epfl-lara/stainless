package stainless
package equivchk

import inox.utils.{NoPosition, Position}
import stainless.AbstractAnalysis
import stainless.extraction.ExtractionSummary
import stainless.verification.VerificationAnalysis
import EquivalenceCheckingReport._

class EquivalenceCheckingAnalysis(val sources: Set[Identifier],
                                  val records: Seq[Record],
                                  val extractionSummary: ExtractionSummary) extends AbstractAnalysis { self =>
  override val name: String = EquivalenceCheckingComponent.name
  override type Report = EquivalenceCheckingReport

  override def toReport: EquivalenceCheckingReport = new EquivalenceCheckingReport(records, sources, extractionSummary)
}
