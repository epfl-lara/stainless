/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package evaluators

import extraction.xlang.{ trees => xt }
import frontend.CallBackWithRegistry

import io.circe.Json

/** Callback for evaluation */
final class EvaluatorCallBack(override val context: inox.Context)
  extends CallBackWithRegistry with EvaluatorCheckFilter {

  override type Report = EvaluatorReport
  override val cacheSubDirectory = EvaluatorComponent.name
  override def parseReportCache(json: Json): Report = EvaluatorReport.parse(json)

  override def onCycleBegin(): Unit = EvaluatorComponent.onCycleBegin()

  override def solve(program: Program { val trees: xt.type }): Report = {
    EvaluatorComponent(program, context).toReport
  }

}

