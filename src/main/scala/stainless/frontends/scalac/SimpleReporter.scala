/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.tools.nsc.Settings
import scala.tools.nsc.reporters.AbstractReporter

import scala.reflect.internal.util.{Position, NoPosition, FakePos, StringOps}
import utils.{Position => LeonPosition, NoPosition => LeonNoPosition, OffsetPosition => LeonOffsetPosition}

/** This implements a reporter that calls the callback with every line that a
regular ConsoleReporter would display. */
class SimpleReporter(val settings: Settings, reporter: leon.Reporter) extends AbstractReporter {
  final val ERROR_LIMIT = 5

  private def label(severity: Severity): String = severity match {
    case ERROR   => "error"
    case WARNING => "warning"
    case INFO    => null
  }

  private def clabel(severity: Severity): String = {
    val label0 = label(severity)
    if (label0 eq null) "" else label0 + ": "
  }

  private def getCountString(severity: Severity): String =
    StringOps.countElementsAsString(severity.count, label(severity))

  /** Prints the message. */
  def printMessage(msg: String, pos: LeonPosition, severity: Severity) {
    severity match {
      case ERROR =>
        reporter.error(pos, msg)
      case WARNING =>
        reporter.warning(pos, msg)
      case INFO =>
        reporter.info(pos, msg)
    }
  }

  /** Prints the message with the given position indication. */
  def printMessage(posIn: Position, msg: String, severity: Severity) {
    val pos = if (posIn eq null) NoPosition
              else if (posIn.isDefined) posIn.finalPosition
              else posIn
    pos match {
      case FakePos(fmsg) =>
        printMessage(fmsg+" "+msg, LeonNoPosition, severity)
      case NoPosition =>
        printMessage(msg, LeonNoPosition, severity)
      case _ =>
        val lpos = LeonOffsetPosition(pos.line, pos.column, pos.point, pos.source.file.file)
        printMessage(msg, lpos, severity)
    }
  }

  def print(pos: Position, msg: String, severity: Severity) {
    printMessage(pos, clabel(severity) + msg, severity)
  }

  def display(pos: Position, msg: String, severity: Severity) {
    severity.count += 1
    if (severity != ERROR || severity.count <= ERROR_LIMIT)
      print(pos, msg, severity)
  }

  def displayPrompt(): Unit = {}
}
