/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import inox.DebugSection

abstract class ReportMessage {
  def sbtPluginOnly: Boolean
  def title: String
  def emit(reporter: inox.Reporter): Unit
}

class DefaultReporter(debugSections: Set[DebugSection]) extends inox.DefaultReporter(debugSections) {
  override def doEmit(msg: Message): Unit = {
    msg.msg match {
      case rm: ReportMessage if rm.sbtPluginOnly => ()
      case _ => super.doEmit(msg)
    }
  }
}

class PlainTextReporter(debugSections: Set[DebugSection]) extends inox.PlainTextReporter(debugSections) {
  override def doEmit(msg: Message): Unit = {
    msg.msg match {
      case rm: ReportMessage if rm.sbtPluginOnly => ()
      case _ => super.doEmit(msg)
    }
  }
}
