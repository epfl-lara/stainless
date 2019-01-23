/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontend

import stainless.extraction.xlang.{trees => xt}

import scala.concurrent.Await
import scala.concurrent.duration._

class BatchedCallBack(components: Seq[Component])(implicit val context: inox.Context) extends CallBack with StainlessReports {
  private var currentClasses = Seq[xt.ClassDef]()
  private var currentFunctions = Seq[xt.FunDef]()

  private var report: AbstractReport[Report] = _

  protected val pipeline: extraction.StainlessPipeline = extraction.pipeline
  private[this] val runs = components.map(_.run(pipeline))

  def beginExtractions(): Unit = {}

  def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    synchronized {
      currentFunctions ++= functions
      currentClasses ++= classes
    }
  }

  def failed(): Unit = {}

  def endExtractions(): Unit = {
    val symbols = xt.NoSymbols.withClasses(currentClasses).withFunctions(currentFunctions)
    val reports = runs.map { run =>
      val result = run(symbols.functions.keys.toSeq, symbols, filterSymbols = true)
      val report = Await.result(result, Duration.Inf).toReport
      RunReport(run)(report)
    }
    report = Report(reports)
  }

  def stop(): Unit = {
    currentClasses = Seq()
    currentFunctions = Seq()
  }

  def join(): Unit = {}

  def getReport = Option(report)
}
