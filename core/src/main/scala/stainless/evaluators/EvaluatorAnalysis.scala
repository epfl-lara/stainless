/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package evaluators

trait EvaluatorAnalysis extends AbstractAnalysis {
  import EvaluatorComponent.Result
  import EvaluatorReport.Record

  val program: StainlessProgram
  val sources: Set[Identifier] // set of functions that were considered for the analysis
  val results: Seq[Result]

  private lazy val records = results map { case Result(fd, status, time) =>
    val textStatus = status match {
      case EvaluatorComponent.BodyFailed(error)       => EvaluatorReport.BodyFailed(error)
      case EvaluatorComponent.PostFailed(body, error) => EvaluatorReport.PostFailed(body.toString, error)
      case EvaluatorComponent.PostInvalid(body)       => EvaluatorReport.PostInvalid(body.toString)
      case EvaluatorComponent.PostHeld(body)          => EvaluatorReport.PostHeld(body.toString)
      case EvaluatorComponent.NoPost(body)            => EvaluatorReport.NoPost(body.toString)
    }
    Record(fd.id, fd.getPos, textStatus, time)
  }

  override type Report = EvaluatorReport
  override val name = EvaluatorComponent.name
  override def toReport = new EvaluatorReport(records, sources)
}

