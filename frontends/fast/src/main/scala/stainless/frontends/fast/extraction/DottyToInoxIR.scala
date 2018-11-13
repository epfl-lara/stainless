package stainless.frontends.fast.extraction

import dotty.tools.dotc.ast.untpd
import stainless.frontends.fast.IRs

trait DottyToInoxIR extends ExtractMods { self: IRs =>
  import Exprs._

  def apply(tree: untpd.Tree): IR = {
    UnitLiteral()
  }
}
