/* Copyright 2009-2019 EPFL, Lausanne */

package stainless

import inox.DebugSection

abstract class ReportMessage {
  def sbtPluginOnly: Boolean
  def toString: String
  def emit(reporter: inox.Reporter): Unit
}

class DefaultReporter(debugSections: Set[DebugSection]) extends inox.DefaultReporter(debugSections) {
  override def emit(msg: Message): Unit = msg.msg match {
    case rm: ReportMessage if rm.sbtPluginOnly => ()
    case _ => super.emit(msg)
  }
}

class PlainTextReporter(debugSections: Set[DebugSection]) extends stainless.DefaultReporter(debugSections)
