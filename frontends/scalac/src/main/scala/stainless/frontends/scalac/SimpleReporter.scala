/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.scalac

import scala.tools.nsc.Settings
import scala.tools.nsc.reporters.FilteringReporter

import scala.reflect.internal.util.{Position, NoPosition, FakePos, StringOps}

/** This implements a reporter that calls the callback with every line that a
  * regular ConsoleReporter would display. */
class SimpleReporter(val settings: Settings, reporter: inox.Reporter) extends FilteringReporter {
  final val ERROR_LIMIT = 5

  val count = scala.collection.mutable.Map[Severity, Int](
    ERROR   -> 0,
    WARNING -> 0,
    INFO    -> 0,
  )

  private def label(severity: Severity): String = {
    // the labels are not stable identifier, as such we cannot directly pattern patch on them, so we must explicitly compare them with ==
    severity match {
      case x if x == ERROR   => "error"
      case x if x == WARNING => "warning"
      case x if x == INFO    => null
      case _                 => throw new Exception("Severity should be one of ERROR, WARNING, INFO")
    }
  }

  private def clabel(severity: Severity): String = {
    val label0 = label(severity)
    if (label0 eq null) "" else label0 + ": "
  }

  private def getCountString(severity: Severity): String =
    StringOps.countElementsAsString(count(severity), label(severity))

  /** Prints the message. */
  def printMessage(msg: String, pos: inox.utils.Position, severity: Severity): Unit = {
    // the labels are not stable identifier, as such we cannot directly pattern patch on them, so we must explicitly compare them with ==
    severity match {
      case x if x == ERROR =>
        reporter.error(pos, msg)
      case x if x == WARNING =>
        reporter.warning(pos, msg)
      case x if x == INFO =>
        reporter.info(pos, msg)
      case _ =>
        throw new Exception("Severity should be one of ERROR, WARNING, INFO")
    }
  }

  /** Prints the message with the given position indication. */
  def printMessage(posIn: Position, msg: String, severity: Severity): Unit = {
    val pos = if (posIn eq null) NoPosition
              else if (posIn.isDefined) posIn.finalPosition
              else posIn
    pos match {
      case FakePos(fmsg) =>
        printMessage(fmsg+" "+msg, inox.utils.NoPosition, severity)
      case NoPosition =>
        printMessage(msg, inox.utils.NoPosition, severity)
      case _ =>
        val lpos = inox.utils.OffsetPosition(pos.line, pos.column, pos.point, pos.source.file.file)
        printMessage(msg, lpos, severity)
    }
  }

  def print(pos: Position, msg: String, severity: Severity): Unit = {
    printMessage(pos, clabel(severity) + msg, severity)
  }

  def display(pos: Position, msg: String, severity: Severity): Unit = {
    count(severity) += 1
    if (severity != ERROR || count(severity) <= ERROR_LIMIT)
      print(pos, msg, severity)
  }

  def displayPrompt(): Unit = {}

  def doReport(pos: Position, msg: String, severity: Severity): Unit =
    printMessage(pos, msg, severity)
}
