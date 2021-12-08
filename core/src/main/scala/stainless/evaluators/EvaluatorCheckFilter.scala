/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package evaluators

import utils.CheckFilter

trait EvaluatorCheckFilter extends CheckFilter {
  import trees._

  override def shouldBeChecked(fd: FunDef): Boolean =
    fd.isParameterless && super.shouldBeChecked(fd)
}

object EvaluatorCheckFilter {
  def apply(t: ast.Trees, ctx: inox.Context): EvaluatorCheckFilter {
    val trees: t.type
  } = {
    class Impl(override val trees: t.type, override val context: inox.Context) extends EvaluatorCheckFilter
    new Impl(t, ctx)
  }
}

