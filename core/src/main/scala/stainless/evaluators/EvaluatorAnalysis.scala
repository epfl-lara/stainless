/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package evaluators

trait EvaluatorAnalysis extends AbstractAnalysis {
  import EvaluatorRun.Result
  import EvaluatorReport.Record

  val program: StainlessProgram
  val sources: Set[Identifier] // set of functions that were considered for the analysis
  val results: Seq[Result]

  private lazy val records = results map { case Result(fd, status, time) =>
    val textStatus = status match {
      case EvaluatorRun.BodyFailed(error)       => EvaluatorReport.BodyFailed(error)
      case EvaluatorRun.PostFailed(body, error) => EvaluatorReport.PostFailed(body.toString, error)
      case EvaluatorRun.PostInvalid(body)       => EvaluatorReport.PostInvalid(body.toString)
      case EvaluatorRun.PostHeld(body)          => EvaluatorReport.PostHeld(body.toString)
      case EvaluatorRun.NoPost(body)            => EvaluatorReport.NoPost(body.toString)
    }
    Record(fd.id, fd.getPos, textStatus, time)
  }

  override type Report = EvaluatorReport
  override val name = EvaluatorComponent.name
  override def toReport = new EvaluatorReport(records, sources)
}

