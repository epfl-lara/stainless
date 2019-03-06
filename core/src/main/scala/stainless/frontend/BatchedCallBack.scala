/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontend

import stainless.extraction.xlang.{trees => xt}

import scala.util.{Try, Success, Failure}
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
    val reports = runs map { run =>
      val ids = symbols.functions.keys.toSeq
      val analysis = Try(run(ids, symbols, filterSymbols = true))
      analysis match {
        case Success(analysis) =>
          val report = Await.result(analysis, Duration.Inf).toReport
          Some(RunReport(run)(report))

        case Failure(err) =>
          context.reporter.error(s"Run has failed with error: $err")
          None
      }
    }
    report = Report(reports collect { case Some(r) => r })
  }

  def stop(): Unit = {
    currentClasses = Seq()
    currentFunctions = Seq()
  }

  def join(): Unit = {}

  def getReport = Option(report)
}
