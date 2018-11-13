package stainless.frontends.fast

import stainless.frontends.dotc.SymbolsContext

trait IRs extends extraction.DottyToInoxIR with inox.parser.IRs {
  def getInoxContext: inox.Context
  def getSymbolCache: SymbolsContext
}
