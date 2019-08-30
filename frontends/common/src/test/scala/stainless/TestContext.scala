/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import inox.{ DebugSection, Options, OptionValue }
import stainless.verification.optVCCache

object TestContext {

  /**
   * Create a context for testing purposes.
   *
   * Unless explicitely present in [[options]], the returned
   * context is set to use no VC cache.
   */
  def apply(options: Options): inox.Context = {
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
  def debug(sections: Set[DebugSection], options: Options): inox.Context = {
    val reporter = new stainless.DefaultReporter(sections)
    val ctx = apply(options)
    inox.Context(reporter, ctx.interruptManager, ctx.options, ctx.timers)
  }

  def debug(sections: Set[DebugSection]): inox.Context = debug(sections, Options.empty)

  def empty: inox.Context = apply(Options.empty)

}


