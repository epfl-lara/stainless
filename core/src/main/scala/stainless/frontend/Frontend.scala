/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontend

/**
 * Abstract compiler, provides all the tools to extract compilation units
 * into a sequence of small, self-contained programs and send them to a
 * [[CallBack]] whenever they are ready.
 */
abstract class Frontend(val callback: CallBack) {
  /** Proceed to extract the trees in a non-blocking way. */
  def run(): Unit

  def isRunning: Boolean

  // Customisation points for subclasses:
  protected def onStop(): Unit
  protected def onJoin(): Unit

  /** Stop the compiler (and wait until it has stopped). */
  final def stop(): Unit = {
    onStop()
    callback.stop()
  }

  /** Wait for the compiler, and the generated tasks, to finish. */
  final def join(): Unit = {
    onJoin()
    callback.join()
  }

  // See assumption/requirements in [[CallBack]]
  final def getReports: Seq[AbstractReport] = {
    assert(!isRunning)
    callback.getReports
  }
}

/** A Frontend factory which takes as input: context + compiler arguments + callback */
trait FrontendFactory {
  def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend

  protected val extraCompilerArguments: Seq[String] = Nil
  protected val libraryFiles: Seq[String]

  /** All the arguments for the underlying compiler. */
  protected def allCompilerArguments(compilerArgs: Seq[String]) =
    extraCompilerArguments ++ libraryFiles ++ compilerArgs
}

