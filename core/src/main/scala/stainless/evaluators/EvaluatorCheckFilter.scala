/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package evaluators

trait EvaluatorCheckFilter extends utils.CheckFilter {
  override def shouldBeChecked(fd: extraction.xlang.trees.FunDef): Boolean =
    fd.isParameterless && super.shouldBeChecked(fd.id, fd.flags)
}

object EvaluatorCheckFilter {
  def apply(ctx: inox.Context) = new EvaluatorCheckFilter {
    override val context = ctx
  }
}

