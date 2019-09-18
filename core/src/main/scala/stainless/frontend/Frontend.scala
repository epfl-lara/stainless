/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package frontend

/**
 * Abstract compiler, provides all the tools to extract compilation units
 * into a sequence of small, self-contained programs and send them to a
 * [[MasterCallBack]] whenever they are ready (the master callback forwards
 * data to each active component's callback).
 *
 * Implementations of [[Frontend]] are required to rethrow exception emitted
 * in background thread (if any) when [[join]] or [[stop]] are invoked.
 */
abstract class Frontend(val callback: CallBack) {
  /** Proceed to extract the trees in a non-blocking way. */
  def run(): Unit

  def isRunning: Boolean

  /** List of files compiled by this frontend, including the library. */
  val sources: Seq[String]

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
  final def getReport: Option[AbstractReport[_]] = {
    assert(!isRunning)
    callback.getReport
  }
}

