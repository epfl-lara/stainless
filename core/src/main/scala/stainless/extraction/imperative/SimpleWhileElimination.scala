/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait SimpleWhileElimination
  extends oo.CachingPhase
    with IdentitySorts
    with SimplyCachedFunctions
    with SimpleFunctions
    with oo.IdentityTypeDefs
    with oo.IdentityClasses
    with utils.SyntheticSorts { self =>

  val s: Trees
  val t: Trees

  protected class TransformerContext(val symbols: s.Symbols) {
    // we precompute the set of expressions that contain a return
    val exprHasReturn = collection.mutable.Set[s.Expr]()
    for (fd <- symbols.functions.values) {
      s.exprOps.postTraversal {
        case e @ s.Return(_) => exprHasReturn += e
        case e @ s.Operator(es, _) if (es.exists(exprHasReturn)) => exprHasReturn += e
        case _ => ()
      }(fd.fullBody)
    }

    val funHasReturn: Set[Identifier] = symbols.functions.values.collect {
      case fd if exprHasReturn(fd.fullBody) => fd.id
    }.toSet

    // and the set of expressions that contain a while
    val exprHasWhile = collection.mutable.Set[s.Expr]()
    for (fd <- symbols.functions.values) {
      s.exprOps.postTraversal {
        case e @ s.While(_, _, _) => exprHasWhile += e
        case e @ s.Operator(es, _) if (es.exists(exprHasWhile)) => exprHasWhile += e
        case _ => ()
      }(fd.fullBody)
    }

    val funHasWhile: Set[Identifier] = symbols.functions.values.collect {
      case fd if exprHasWhile(fd.fullBody) => fd.id
    }.toSet
  }

  /* Extract functional result value. Useful to remove side effect from conditions when moving it to post-condition */
  def getFunctionalResult(expr: t.Expr): t.Expr = t.exprOps.postMap {
    case t.Block(_, res) => Some(res)
    case _ => None
  }(expr)

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected def extractFunction(tc: TransformerContext, fd: s.FunDef): t.FunDef = {
    implicit val symboms = tc.symbols

    // we transform `fd` if the function contains a "simple" `While` loop with no return inside
    val transform = s.exprOps.exists {
      case wh @ s.While(_, _, _) => !tc.exprHasReturn(wh)
      case _ => false
    } (fd.fullBody)

    if (transform) {
      object WhileTransformer extends transformers.TreeTransformer {
        override val s: self.s.type = self.s
        override val t: self.t.type = self.t

        override def transform(expr: s.Expr): t.Expr = expr match {
          case wh @ s.While(cond, body, optInv)
            if !tc.exprHasReturn(cond) && !tc.exprHasReturn(body) && optInv.forall(inv => !tc.exprHasReturn(inv)) =>

            val transformedCond = transform(cond)
            val transformedBody = transform(body)
            val transformedInv = optInv.map(transform)

            val id = FreshIdentifier(fd.id.name + "While")
            val tpe = t.FunctionType(Seq(), t.UnitType().copiedFrom(wh)).copiedFrom(wh)

            val specced = t.exprOps.BodyWithSpecs(transformedBody)
            val measure = specced.getSpec(t.exprOps.MeasureKind).map(_.expr)

            val ite =
              t.IfExpr(
                transformedCond,
                t.ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
                t.UnitLiteral().copiedFrom(wh)
              ).copiedFrom(wh)

            val newBody =
              t.Block(
                Seq(specced.body),
                ite
              ).copiedFrom(wh)

            val newPost =
              t.Lambda(
                Seq(t.ValDef.fresh("_unused", t.UnitType().copiedFrom(wh)).copiedFrom(wh)),
                t.and(
                  t.Not(getFunctionalResult(transformedCond).copiedFrom(cond)).copiedFrom(cond),
                  transformedInv.getOrElse(t.BooleanLiteral(true).copiedFrom(wh))
                ).copiedFrom(wh)
              ).copiedFrom(wh)

            val fullBody = t.exprOps.withPostcondition(
              t.exprOps.withPrecondition(
                t.exprOps.withMeasure(newBody, measure).copiedFrom(wh),
                Some(t.andJoin(transformedInv.toSeq :+ getFunctionalResult(transformedCond)))
              ).copiedFrom(wh),
              Some(newPost)
            ).copiedFrom(wh)

            t.LetRec(
              Seq(t.LocalFunDef(id, Seq(), Seq(), t.UnitType().copiedFrom(wh), fullBody, Seq()).copiedFrom(wh)),
              t.IfExpr(
                transformedCond,
                t.ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
                t.UnitLiteral().copiedFrom(wh)
              ).copiedFrom(wh)
            ).copiedFrom(wh)

          case _ => super.transform(expr)
        }
      }

      new t.FunDef(
        fd.id,
        fd.tparams.map(WhileTransformer.transform),
        fd.params.map(WhileTransformer.transform),
        WhileTransformer.transform(fd.returnType),
        WhileTransformer.transform(fd.fullBody),
        fd.flags.map(WhileTransformer.transform)
      ).setPos(fd)
    }
    else {
      new CheckingTransformer {
        override val s: self.s.type = self.s
        override val t: self.t.type = self.t
      }.transform(fd)
    }
  }
}

object SimpleWhileElimination {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new SimpleWhileElimination {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
