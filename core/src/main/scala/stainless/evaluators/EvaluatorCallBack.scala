/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package evaluators

import extraction.xlang.{ trees => xt }
import frontend.CallBackWithRegistry

import scala.concurrent.Future

import io.circe.Json

/** Callback for evaluation */
final class EvaluatorCallBack(override implicit val context: inox.Context)
  extends CallBackWithRegistry with EvaluatorCheckFilter {

  override type Report = EvaluatorReport
  override val cacheSubDirectory = EvaluatorComponent.name
  override def parseReportCache(json: Json): Report = EvaluatorReport.parse(json)

  override def onCycleBegin(): Unit = EvaluatorComponent.onCycleBegin()

  override def solve(program: Program { val trees: xt.type }): Future[Report] = {
    EvaluatorComponent(program, context).map(_.toReport)
  }

}

