/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import inox.DebugSection

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
