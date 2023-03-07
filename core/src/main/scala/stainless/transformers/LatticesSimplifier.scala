package stainless
package transformers

import inox.solvers

import java.util.concurrent.atomic.AtomicInteger

// Wrapper that sets up a thread-local algo instance
trait LatticesSimplifier { self =>
  import LatticesSimplifier._
  val trees: ast.Trees
  val symbols: trees.Symbols
  val opts: solvers.PurityOptions
  val algo: UnderlyingAlgo

  import trees._
  import symbols.{given, _}

  private def newAlgo(): lattices.Core{val trees: self.trees.type; val symbols: self.symbols.type} = algo match {
    case UnderlyingAlgo.OCBSL => lattices.OCBSL(trees, symbols, opts)
    case UnderlyingAlgo.OL => lattices.OL(trees, symbols, opts)
    case UnderlyingAlgo.Bland => lattices.Bland(trees, symbols, opts)
  }
  private val coreTL: ThreadLocal[lattices.Core{val trees: self.trees.type; val symbols: self.symbols.type}] =
    ThreadLocal.withInitial(() => newAlgo())

  def simplify(e: Expr): Expr = {
    val core = coreTL.get()
    given core.Env = core.Env.empty
    given core.Ctxs = core.Ctxs.empty
    given core.LetValSubst = core.LetValSubst.empty

    val resE = core.codeOfExpr(e)
    val codeE = resE.selfPlugged(core.Ctxs.empty)._2
    val result = core.uncodeOf(codeE).expr.copiedFrom(e)
    core.shouldRetire() match {
      case core.Retirement.KeepGoing =>
        core.clearCaches()
      case core.Retirement.WellDeserved(fnPurityCache) =>
        // So long, `core` instance
        val newInst = newAlgo()
        newInst.setFunctionPurityCache(fnPurityCache)
        coreTL.set(newInst)
    }
    result
  }
}
object LatticesSimplifier {

  enum UnderlyingAlgo {
    case OCBSL
    case OL
    case Bland
  }

  def apply(t: ast.Trees, s: t.Symbols, opts: solvers.PurityOptions, algo: UnderlyingAlgo): LatticesSimplifier{val trees: t.type; val symbols: s.type} = {
    class Impl(override val trees: t.type, override val symbols: s.type, override val opts: solvers.PurityOptions, override val algo: UnderlyingAlgo) extends LatticesSimplifier
    new Impl(t, s, opts, algo)
  }
}