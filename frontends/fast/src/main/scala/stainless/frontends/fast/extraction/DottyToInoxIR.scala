package stainless.frontends.fast.extraction

import dotty.tools.dotc.ast.untpd
import dotty.tools.dotc.core.Contexts
import stainless.frontends.fast.IRs

trait DottyToInoxIR extends ExtractMods { self: IRs =>
  implicit var ctx: Contexts.Context = _

  def withDottyContext(ctx: Contexts.Context): Unit = this.ctx = ctx

  import Exprs._

  def extractToInox(tree: untpd.Tree): IR = {
    UnitLiteral()
  }
}
