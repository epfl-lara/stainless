/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

trait ChooseEncoder extends CachingPhase with SimplyCachedFunctions with IdentitySorts { self =>

  implicit val context: inox.Context
  val s: Trees
  val t: s.type = s
  import s._

  type TransformerContext = Symbols
  override def getContext(symbols: Symbols) = symbols

  override protected type FunctionResult = Seq[FunDef]
  override protected def registerFunctions(symbols: Symbols, functions: Seq[Seq[FunDef]]): Symbols =
    symbols.withFunctions(functions.flatten)

  protected def extractFunction(context: TransformerContext, fd: FunDef): Seq[FunDef] = {
    var fdChooses = Seq[FunDef]()

    def rec(e: Expr, params: Seq[ValDef]): Expr = e match {
      case l: Let => l.copy(body = rec(l.body, params :+ l.vd)).copiedFrom(l)

      case l: Lambda => l.copy(body = rec(l.body, params ++ l.params)).copiedFrom(l)

      case c @ Choose(vd, pred) =>
        val (substMap, freshParams) = params.foldLeft((Map[ValDef, Expr](), Seq[ValDef]())) {
          case ((substMap, vds), vd) =>
            val ntpe = typeOps.replaceFromSymbols(substMap, vd.tpe)
            val nvd = ValDef(vd.id.freshen, ntpe, vd.flags).copiedFrom(vd)
            (substMap + (vd -> nvd.toVariable), vds :+ nvd)
        }

        val returnType = typeOps.replaceFromSymbols(substMap, vd.tpe)
        val newVd = vd.copy(tpe = returnType).setPos(vd)
        val newPred = exprOps.replaceFromSymbols(substMap, rec(pred, params :+ vd))
        val newChoose = Choose(newVd, newPred).copiedFrom(c)

        val newFd = new FunDef(
          FreshIdentifier("choose", true), fd.tparams, freshParams,
          returnType,
          newChoose,
          Seq(Derived(Some(fd.id)), DropVCs),
        ).setPos(fd)

        fdChooses = fdChooses :+ newFd

        Assert(
          Not(Forall(Seq(vd), Not(pred).setPos(c)).setPos(c)).setPos(c),
          Some("Choose satisfiability"),
          FunctionInvocation(newFd.id, newFd.tparams.map(_.tp), params.map(_.toVariable)).copiedFrom(c)
        ).setPos(c)

      case Operator(es, recons) => recons(es.map(rec(_, params))).copiedFrom(e)
    }

    // bind `newFd` before returning so that `fdChooses` gets filled with the new `choose` functions
    val newFd = fd.copy(fullBody = rec(fd.fullBody, fd.params)).setPos(fd)
    fdChooses :+ newFd
  }

}

object ChooseEncoder {
  def apply(it: inlining.Trees)(implicit ctx: inox.Context): ChooseEncoder {
    val s: it.type
    val t: it.type
  } = new ChooseEncoder {
    override val context = ctx
    override val s: it.type = it
    override val t: it.type = it
  }
}
