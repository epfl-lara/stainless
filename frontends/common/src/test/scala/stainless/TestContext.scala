/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import inox.{ Context, DebugSection, Options, OptionValue }
import stainless.verification.optVCCache

object TestContext {

  /**
   * Create a context for testing purposes.
   *
   * Unless explicitely present in [[options]], the returned
   * context is set to use no VC cache.
   */
  def apply(options: Options): Context = {
    val newOptions =
      if ((options findOption optVCCache).isDefined) options
      else options + OptionValue(optVCCache)(false)
    inox.TestContext(newOptions)
  }

  /**
   * Use for debug purposes.
   *
   * The returned context has a DefaultReporter.
   **/
  def debug(sec: DebugSection, options: Options): Context = {
    val reporter = new inox.DefaultReporter(Set(sec))
    val ctx = apply(options)
    Context(reporter, ctx.interruptManager, ctx.options, ctx.timers)
  }

  def debug(sec: DebugSection): Context = debug(sec, Options.empty)

  def empty: Context = apply(Options.empty)

}


