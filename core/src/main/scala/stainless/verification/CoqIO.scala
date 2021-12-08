package stainless
package verification

import scala.sys.process._
import scala.language.postfixOps
import java.io.FileWriter
import java.nio.file.{Files, Paths}
import java.util.concurrent.TimeUnit

import scala.collection.mutable.ListBuffer
import scala.concurrent.{Await, Future, TimeoutException}
import scala.concurrent.duration.Duration
import scala.concurrent.ExecutionContext.Implicits.global

object CoqIO {
  // this global variable makes sure that no two files with the same name are created
  var i = 0

  val fileName = "verif"
  
  given givenDebugSection: DebugSectionCoq.type = DebugSectionCoq

  val outputDirectory = "tmp"

  def writeToCoqFile(file: String, c: CoqCommand): Unit = {
    val s = new FileWriter(file)
    s.write(c.coqString)
    s.close()
  }

  def makeOutputDirectory(): Unit = {
    val path = Paths.get(outputDirectory)
    if (!Files.exists(path))
      Files.createDirectory(path)
  }

  def makeFilename(name: String): String = s"$outputDirectory/$name.v"

  def writeToCoqFile(c: CoqCommand): String = {
    this.synchronized {
      i += 1 // we atomically increment this variable
    }
    val file = s"$fileName$i.v"
    writeToCoqFile(file,c)
    file
  }

  def writeToCoqFile(m: Seq[(String, CoqCommand)]): Seq[String] = {
    val filenames = m.map {case (name, command) => (makeFilename(name), command)}
    filenames.foreach {case (fname, command) => writeToCoqFile(fname, command)}
    filenames.map(_._1)
  }

  def coqc(fileName: String, ctx: inox.Context): CoqStatus = {
    ctx.reporter.info(s"Verifying file $fileName")
    val output:ListBuffer[String] = new collection.mutable.ListBuffer[String]
    val proc: Process = s"coqc -R slc-lib SLC $fileName" run ProcessLogger(output += _)

    val timeout: Duration = ctx.options.findOption(inox.optTimeout) match {
      case Some(to) => to
      case None => Duration.create(1200, TimeUnit.SECONDS) //20mins
    }

    try {
      Await.result(Future(proc.exitValue()), timeout)
      if (output.isEmpty) {
        ctx.reporter.info(s"No output from Coq for file $fileName. Your program is valid.")
        CoqStatus.Valid
      }
      else {
        ctx.reporter.info(s"Coq gave some output for file $fileName:")
        val l = output.mkString("\n")
        if (l.contains("Error")) {
          ctx.reporter.error(l)
          if (l.contains("Timeout")) {
            CoqStatus.Timeout
          } else if (l.contains("The command has not failed")) {
            CoqStatus.Invalid
          } else if (l.contains("Universe Top")) { //TODO check for greatest common part of the bug
            CoqStatus.ExternalBug
          } else {
            //something unexpected
            CoqStatus.InternalError
          }
        }
        else if (l.trim != "") {
          ctx.reporter.warning(l)
          CoqStatus.Unknown
        } else {
          CoqStatus.Unknown
        }
      }
    } catch {
      case _: TimeoutException => {
        ctx.reporter.warning("Timeout!")
        proc.destroy()
        CoqStatus.Timeout
      }
    }
  }
}

class CoqStatus {}

object CoqStatus {
  case object Invalid extends CoqStatus
  case object Valid extends CoqStatus
  case object Unknown extends CoqStatus
  case object Timeout extends CoqStatus
  case object Cancelled extends CoqStatus
  case object InternalError extends CoqStatus
  case object ExternalBug extends CoqStatus
}