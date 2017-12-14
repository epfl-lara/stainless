/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package evaluators

import frontend.CallBackWithRegistry
import utils.CheckFilter

import io.circe.Json

/** Callback for evaluation */
final class EvaluatorCallBack(override val context: inox.Context)
  extends CallBackWithRegistry with CheckFilter {

  override type Report = EvaluatorReport
  override val cacheSubDirectory = EvaluatorComponent.name
  override def parseReportCache(json: Json): Report = EvaluatorReport.parse(json)

  override def onCycleBegin(): Unit = EvaluatorComponent.onCycleBegin()

  override def solve(program: Program { val trees: extraction.xlang.trees.type }): Report = {
    EvaluatorComponent(program, context).toReport
  }

}

