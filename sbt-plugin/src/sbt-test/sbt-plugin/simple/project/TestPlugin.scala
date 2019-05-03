// copied from https://github.com/sbt/sbt-zero-thirteen/blob/0.13/sbt/src/sbt-test/compiler-project/semantic-errors/project/src/main/scala/sbt/TestPlugin.scala
package sbt

import Keys._
import xsbti.{Position, Severity}

object TestPlugin extends AutoPlugin {
  override def requires = plugins.JvmPlugin
  override def trigger = allRequirements

  object autoImport {
    val savedReporter = settingKey[xsbti.Reporter]("Saved reporter that collects compilation failures.")
    val problems = taskKey[Array[xsbti.Problem]]("Problems reported during compilation.")
  }
  import autoImport._
  override def projectSettings = Seq(
    savedReporter := new CollectingReporter,
    compilerReporter in (Compile, compile) := savedReporter.value,
    problems := savedReporter.value.problems
  )
}

class CollectingReporter extends xsbti.Reporter {
  private val buffer = collection.mutable.ArrayBuffer.empty[xsbti.Problem]

  def reset(): Unit = synchronized {
    //System.err.println(s"DEBUGME: Clearing errors: $buffer")
    buffer.clear()
  }
  def hasErrors: Boolean = synchronized { buffer.exists(_.severity == Severity.Error) }
  def hasWarnings: Boolean = synchronized { buffer.exists(_.severity == Severity.Warn) }
  def printSummary(): Unit = ()
  def problems: Array[xsbti.Problem] = synchronized { buffer.toArray }

  /** Logs a message. */
  def log(problem: xsbti.Problem): Unit = synchronized { buffer.append(problem) }

  /** Reports a comment. */
  def comment(pos: xsbti.Position, msg: String): Unit = ()

  override def toString = "CollectingReporter"
}
