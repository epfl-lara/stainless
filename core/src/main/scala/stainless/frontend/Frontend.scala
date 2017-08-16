/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontend

/** An exception thrown when non-purescala compatible code is encountered. */
sealed class UnsupportedCodeException(val pos: inox.utils.Position, msg: String)
  extends Exception(msg)

/**
 * Abstract compiler, provides all the tools to extract compilation units
 * into a sequence of small, self-contained programs and send them to a
 * [[CallBack]] whenever they are ready.
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
  final def getReports: Seq[AbstractReport] = {
    assert(!isRunning)
    callback.getReports
  }
}


/**
 * Provide a generic implementation for frontends that require a thread-based
 * environment to be non-blocking.
 *
 * If an exception is thrown from within the compiler, it is re-thrown upon
 * stopping or joining.
 */
abstract class ThreadedFrontend(callback: CallBack, ctx: inox.Context) extends Frontend(callback) {
  private var thread: Thread = _
  private var exception: Throwable = _

  protected def initRun(): Unit // Called when initializing the thread (before callback initialisation).
  protected def onRun(): Unit // Called when the thread is running (after callback initialisation).
  protected def onEnd(): Unit // Called when the thread successfully ends (after callback cleanup).
  protected def onStop(thread: Thread): Unit // Called when the user wants to interrupt the frontend.

  final override def run(): Unit = {
    assert(!isRunning)

    val runnable = new Runnable {
      override def run(): Unit = try {
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
      override def uncaughtException(t: Thread, e: Throwable): Unit = exception = e
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

  private def rethrow(): Unit = if (exception != null) {
    val e = exception
    exception = null
    ctx.reporter.error(s"Rethrowing exception emitted from within the compiler: ${e.getMessage}")
    throw e
  }
}


/** A Frontend factory which takes as input: context + compiler arguments + callback */
trait FrontendFactory {
  def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend

  protected val extraCompilerArguments: Seq[String] = Nil
  protected val libraryFiles: Seq[String]

  /** All the arguments for the underlying compiler. */
  protected def allCompilerArguments(compilerArgs: Seq[String]): Seq[String] =
    extraCompilerArguments ++ libraryFiles ++ compilerArgs
}

