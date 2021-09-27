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

      case c: Choose =>
        val (substMap, freshParams) = params.foldLeft((Map[ValDef, Expr](), Seq[ValDef]())) {
          case ((substMap, vds), vd) =>
            val ntpe = typeOps.replaceFromSymbols(substMap, vd.tpe)
            val nvd = ValDef(vd.id.freshen, ntpe, vd.flags).copiedFrom(vd)
            (substMap + (vd -> nvd.toVariable), vds :+ nvd)
        }

        val newPred = exprOps.replaceFromSymbols(substMap, rec(c.pred, params :+ c.res))
        val returnType = typeOps.replaceFromSymbols(substMap, c.res.tpe)

        val newFd = new FunDef(
          FreshIdentifier("choose", true), fd.tparams, freshParams,
          returnType,
          Choose(c.res.copy(tpe = returnType), newPred).copiedFrom(c),
          Seq(Derived(Some(fd.id)))
        ).setPos(fd)

        fdChooses :+= newFd

        FunctionInvocation(newFd.id, newFd.tparams.map(_.tp), params.map(_.toVariable)).copiedFrom(c)

      case Operator(es, recons) => recons(es.map(rec(_, params))).copiedFrom(e)
    }

    val res = fd.copy(fullBody = fd.fullBody match {
      // case c: Choose => c.copy(pred = rec(c.pred, fd.params)).copiedFrom(c)
      case body => rec(body, fd.params)
    }).setPos(fd)

    fdChooses :+ res
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
