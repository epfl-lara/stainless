package stainless
package transformers
package lattices

import inox.solvers

trait Bland extends Core {
  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._

  override final def impliedImpl(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = false

  override final def doSimplifyDisjunction(disjs: Seq[Code], polarity: Boolean)(using Env, Ctxs): Seq[Code] = disjs

  override final def checkForDisjunctionContradiction(disjs0: Seq[Code])(using Env, Ctxs): Option[Int] = None
}

object Bland {
  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions): Bland{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions) extends Bland
    new Impl(t, s, opts)
  }
}