/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package frontend

import java.nio.file.{Files, Paths}
import scala.io.StdIn
import io.circe.Json

class InteractiveRunner(ctx: inox.Context, factory: FrontendFactory) {
  def run(): Unit = {
    val reporter = ctx.reporter
    reporter.info(s"\n\nWaiting for interactive input...\n\n")

    // Make the main loop interruptible
    var loop = true
    val interruptible = new inox.utils.Interruptible {
      override def interrupt(): Unit = { loop = false }
    }
    ctx.interruptManager.registerForInterrupts(interruptible)

    // The main loop

    def emitError(msg: String) = {
      reporter.error(msg)
      val fields = List(
        "status" -> Json.fromString("Error"),
        "msg" -> Json.fromString(msg)
      )
      println(Json.fromFields(fields).spaces2)
    }

    def emitSuccess(reports: Json) = {
      reporter.info("Successfully processed query.")
      val fields = List(
        "status" -> Json.fromString("Success"),
        "reports" -> reports
      )
      println(Json.fromFields(fields).spaces2)
    }

    def newCompiler(sourceFile: String) =
      frontend.build(ctx, Seq(sourceFile), factory)
    var compiler: Frontend = null

    // Read a JSON query, feed it to the frontend, print the JSON report
    while (loop) {
      val sourceFile: String = StdIn.readLine()
      if (sourceFile == null) {
        reporter.info(s"End of input reached. Stopping...")
        loop = false;
      } else if (Files.isReadable(Paths.get(sourceFile))) {
        reporter.info(s"Processing $sourceFile...")

        try {
          compiler = newCompiler(sourceFile)
          compiler.run()
          compiler.join()

          // Write to log file
          compiler.getReport foreach { _.emit(ctx) }

          // Emit JSON report
          val report = compiler.getReport
          report match {
            case Some(report) => emitSuccess(report.emitJson)
            case None => emitError("No report was produced!")
          }

        } catch {
          case e: Throwable =>
            reporter.debug(e)(frontend.DebugSectionFrontend)
            emitError(
              Option(e.getMessage).getOrElse("There was an error while processing the query!")
            )
        }
      } else {
        emitError(s"Cannot read $sourceFile!")
      }
    }
  }
}
