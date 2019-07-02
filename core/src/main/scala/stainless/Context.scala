/* Copyright 2009-2019 EPFL, Lausanne */

package stainless

import inox.utils.InterruptManager

object Context {
  def empty = {
    val reporter = new stainless.DefaultReporter(Set())
    inox.Context(reporter, new InterruptManager(reporter))
  }

  def withReporter(reporter: inox.Reporter)(ctx: inox.Context): inox.Context = {
    ctx.copy(
      reporter = reporter,
      interruptManager = new inox.utils.InterruptManager(reporter),
    )
  }
}
