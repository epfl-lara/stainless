/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

/**
 * Provide a generic implementation for frontends that require a thread-based
 * environment to be non-blocking.
 *
 * If an exception is thrown from within the compiler, it is re-thrown upon
 * stopping or joining.
 */
abstract class ThreadedFrontend(callback: CallBack, ctx: inox.Context) extends Frontend(callback) {
  private given givenDebugSection: DebugSectionFrontend.type = DebugSectionFrontend

  private var thread: Thread = _
  private val exceptions = new scala.collection.mutable.ListBuffer[Throwable]

  protected def initRun(): Unit // Called when initializing the thread (before callback initialisation).
  protected def onRun(): Unit // Called when the thread is running (after callback initialisation).
  protected def onEnd(): Unit // Called when the thread successfully ends (after callback cleanup).
  protected def onStop(thread: Thread): Unit // Called when the user wants to interrupt the frontend.

  final override def run(): Unit = {
    assert(!isRunning)

    val runnable = new Runnable {
      override def run(): Unit = try {
        exceptions.clear()
        initRun()
        callback.beginExtractions()
        onRun()
      } finally {
        callback.endExtractions()
        onEnd()
      }
    }

    thread = new Thread(runnable, "stainless frontend")
    thread.setUncaughtExceptionHandler(new Thread.UncaughtExceptionHandler() {
      override def uncaughtException(t: Thread, e: Throwable): Unit = {
        ThreadedFrontend.this.synchronized(exceptions += e)
      }
    })

    thread.start()
  }

  final override def isRunning: Boolean = thread != null && thread.isAlive

  final override def onStop(): Unit = {
    if (isRunning) onStop(thread)

    rethrow()
  }

  final override def onJoin(): Unit = {
    if (isRunning) thread.join()

    rethrow()
  }

  private def rethrow(): Unit = for (ex <- exceptions) ex match {
    case UnsupportedCodeException(pos, msg) =>
      ctx.reporter.error(pos, msg)
    case _ =>
      ctx.reporter.debug(s"Rethrowing exception emitted from within the compiler: ${ex.getMessage}")
      exceptions.clear()
      throw ex
  }
}

