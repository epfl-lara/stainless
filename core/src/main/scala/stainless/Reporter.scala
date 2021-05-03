/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import java.io.{File, PrintWriter}

import inox.DebugSection
import inox.utils._

abstract class ReportMessage {
  def sbtPluginOnly: Boolean
  def title: String
  def emit(reporter: inox.Reporter): Unit
}

class DefaultReporter(debugSections: Set[DebugSection]) extends inox.DefaultReporter(debugSections) {
  var printingProgress = false

  override def emit(msg: Message): Unit = synchronized {
    if (printingProgress) {
      println()
      printingProgress = false
    }
    msg.msg match {
      case rm: ReportMessage if rm.sbtPluginOnly => ()
      case _ => super.emit(msg)
    }
  }

  override def onCompilerProgress(current: Int, total: Int): Unit = synchronized {
    printingProgress = true
    print("\r" + severityToPrefix(INFO) + s" Verified: $current / $total")
  }
}

class PlainTextReporter(debugSections: Set[DebugSection]) extends inox.PlainTextReporter(debugSections) {
  var printingProgress = false

  override def emit(msg: Message): Unit = synchronized {
    if (printingProgress) {
      println()
      printingProgress = false
    }
    msg.msg match {
      case rm: ReportMessage if rm.sbtPluginOnly => ()
      case _ => super.emit(msg)
    }
  }

  override def onCompilerProgress(current: Int, total: Int): Unit = synchronized {
    printingProgress = true
    print(s"\rVerified: $current / $total")
  }
}

// TODO: Make `println` overridable in inox.DefaultReporter, so we don't duplicate code from it here.
class FilePlainTextReporter(file: File, debugSections: Set[DebugSection]) extends PlainTextReporter(debugSections) {
  protected val writer = new PrintWriter(file)

  def printLine(str: String): Unit = {
    writer.println(str)
    writer.flush()
  }

  override def emit(msg: Message) = synchronized {
    printLine(reline(severityToPrefix(msg.severity), Position.smartPos(msg.position) + msg.msg.toString))
    printLineContent(msg.position)
  }

  def printLineContent(pos: Position): Unit = {
    getLine(pos) match {
      case Some(line) =>
        printLine(blankPrefix+line)
        pos match {
          case rp: RangePosition =>
            val bp = rp.focusBegin
            val ep = rp.focusEnd

            val carret = if (bp.line == ep.line) {
              val width = Math.max(ep.col - bp.col, 1)
              "^" * width
            } else {
              val width = Math.max(line.length+1-bp.col, 1)
              ("^" * width)+"..."
            }

            printLine(blankPrefix+(" " * (bp.col - 1) + carret))

          case op: OffsetPosition =>
            printLine(blankPrefix+(" " * (op.col - 1) + "^"))
        }
      case None =>
    }
  }
}
