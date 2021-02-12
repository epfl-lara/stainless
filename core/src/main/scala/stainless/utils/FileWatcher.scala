/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.utils

import java.io.{ File, PrintWriter }
import java.util.concurrent.TimeUnit

import scala.collection.JavaConverters._
import scala.collection.mutable.{ Map => MutableMap }
import scala.io.{Source, BufferedSource}
import scala.concurrent.Future


/**
 * Facility to run an [[action]] whenever any of the given [[files]] are updated.
 *
 * The [[files]] should refer to absolute paths.
 */
class FileWatcher(ctx: inox.Context, files: Set[File], action: () => Unit) {

  def run(): Unit = {
    val times = MutableMap[File, Long]() ++ (files map { f => f -> f.lastModified })

    ctx.reporter.info(s"\n\nWaiting for source changes... (or press Enter to reload)\n\n")


    var loop = true
    val interruptible = new inox.utils.Interruptible {
      override def interrupt(): Unit = { loop = false }
    }
    ctx.interruptManager.registerForInterrupts(interruptible)

    val keyboard: BufferedSource = Source.stdin
    Future {
      while (loop) {
        keyboard.next()
        ctx.reporter.info(s"Detected Enter key press")
        ctx.interruptManager.unregisterForInterrupts(interruptible)
        action()
        ctx.interruptManager.registerForInterrupts(interruptible)
        ctx.reporter.info(s"\n\nWaiting for source changes... (or press Enter to reload)\n\n")
      }
    } (stainless.multiThreadedExecutionContext)

    while (loop) {
      // Wait for further changes, filtering out everything that is not of interest
      Thread.sleep(500)

      // Update the timestamps while looking for things to process.
      // Note that timestamps are not 100% perfect filters: the files could have the same content.
      // But it's very lightweight and the rest of the pipeline should be able to handle similar
      // content anyway.
      var proceed = false
      for {
        f <- files
        if f.lastModified > times(f)
      } {
        proceed = true
        times(f) = f.lastModified
      }

      if (proceed) {
        ctx.reporter.info(s"Detected file modifications")
        // Wait a little bit to avoid reading incomplete files from disk
        Thread.sleep(100)
        ctx.interruptManager.unregisterForInterrupts(interruptible)
        action()
        ctx.interruptManager.registerForInterrupts(interruptible)
        ctx.reporter.info(s"\n\nWaiting for source changes... (or press Enter to reload)\n\n")
      }
    }

    ctx.interruptManager.unregisterForInterrupts(interruptible)
  }

}

