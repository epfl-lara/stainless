/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait ReturnElimination
  extends oo.CachingPhase
    with IdentitySorts
    with SimplyCachedFunctions
    with SimpleFunctions
    with oo.IdentityTypeDefs
    with oo.IdentityClasses
    with utils.SyntheticSorts { self =>

  val s: Trees
  val t: s.type

  import s._
  import exprOps._

  protected class TransformerContext(val symbols: Symbols) {
    // we precompute the set of expressions that contain a return
    val exprHasReturn = collection.mutable.Set[Expr]()
    for (fd <- symbols.functions.values) {
      postTraversal {
        case e @ Return(_) => exprHasReturn += e
        case e @ Operator(es, _) if (es.exists(exprHasReturn)) => exprHasReturn += e
        case _ => ()
      }(fd.fullBody)
    }

    val funHasReturn: Set[Identifier] = symbols.functions.values.collect {
      case fd if exprHasReturn(fd.fullBody) => fd.id
    }.toSet
  }

  /* Extract functional result value. Useful to remove side effect from conditions when moving it to post-condition */
  def getFunctionalResult(expr: Expr): Expr = postMap {
    case Block(_, res) => Some(res)
    case _ => None
  }(expr)

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  protected def extractFunction(tc: TransformerContext, fd: FunDef): FunDef = {
    implicit val symboms = tc.symbols

    if (tc.funHasReturn(fd.id)) {
      val specced = BodyWithSpecs(fd.fullBody)
      val retType = fd.returnType

      object ReturnTransformer extends TransformerWithType {
        override val s: self.s.type = self.s
        override val t: self.s.type = self.s
        override val symbols: s.Symbols = tc.symbols

        private def proceedOrTransform(expr: Expr, currentType: Type): Expr = {
          if (tc.exprHasReturn(expr)) transform(expr, currentType)
          else ControlFlowSort.proceed(retType, currentType, expr)
        }

        private def proceedOrTransform(mc: MatchCase, currentType: Type): MatchCase = {
          val MatchCase(pattern, optGuard, rhs) = mc
          MatchCase(pattern, optGuard, proceedOrTransform(rhs, currentType))
        }

        override def transform(expr: Expr, currentType: Type): Expr = expr match {
          case wh @ While(cond, body, optInv)
            if !tc.exprHasReturn(cond) && optInv.forall(inv => !tc.exprHasReturn(inv)) =>

            assert(tc.exprHasReturn(body),
              "While loops without `return` must transformed in the `SimpleWhileElimination` phase"
            )

            val id = FreshIdentifier(fd.id.name + "While")
            val loopType = ControlFlowSort.controlFlow(retType, UnitType())
            val tpe = FunctionType(Seq(), loopType.copiedFrom(wh)).copiedFrom(wh)

            val specced = BodyWithSpecs(body)
            val measure = specced.getSpec(MeasureKind).map(_.expr)

            val ite =
              IfExpr(
                cond,
                ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
                ControlFlowSort.proceed(retType, UnitType(), UnitLiteral()).copiedFrom(wh)
              ).copiedFrom(wh)

            val newBody =
              ControlFlowSort.andThen(retType, UnitType(), UnitType(),
                transform(specced.body, UnitType()),
                _ => ite,
                wh.getPos
              )

            val cfWhileVal = ValDef.fresh("cfWhile", loopType.copiedFrom(wh)).copiedFrom(wh)
            val newPost =
              Lambda(
                Seq(cfWhileVal),
                ControlFlowSort.buildMatch(retType, UnitType(), cfWhileVal.toVariable,
                  _ => optInv.getOrElse(BooleanLiteral(true).copiedFrom(wh)),
                  _ => and(
                    Not(getFunctionalResult(cond).copiedFrom(cond)).copiedFrom(cond),
                    optInv.getOrElse(BooleanLiteral(true).copiedFrom(wh))
                  ),
                  wh.getPos
                )
              ).copiedFrom(wh)

            val fullBody = withPostcondition(
              withPrecondition(
                withMeasure(newBody, measure).copiedFrom(wh),
                Some(andJoin(optInv.toSeq :+ getFunctionalResult(cond)))
              ).copiedFrom(wh),
              Some(newPost)
            ).copiedFrom(wh)

            LetRec(
              Seq(LocalFunDef(id, Seq(), Seq(), loopType.copiedFrom(wh), fullBody, Seq()).copiedFrom(wh)),
              IfExpr(
                cond,
                ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
                ControlFlowSort.proceed(retType, UnitType(), UnitLiteral()).copiedFrom(wh)
              ).copiedFrom(wh)
            ).copiedFrom(wh)

          case _ if !tc.exprHasReturn(expr) => expr

          case Assert(e, err, rest) if !tc.exprHasReturn(e) =>
            Assert(e, err, transform(rest, currentType)).setPos(expr)

          case Assume(e, rest) if !tc.exprHasReturn(e) =>
            Assume(e, transform(rest, currentType)).setPos(expr)

          case Return(e) if !tc.exprHasReturn(e) => ControlFlowSort.ret(retType, currentType, e)

          case IfExpr(cond, e1, e2) if !tc.exprHasReturn(cond) =>
            IfExpr(cond,
              proceedOrTransform(e1, currentType),
              proceedOrTransform(e2, currentType)
            ).setPos(expr)

          case MatchExpr(scrut, cases) if !tc.exprHasReturn(scrut) =>
            MatchExpr(scrut,
              cases.map(proceedOrTransform(_, currentType))
            ).setPos(expr)

          case Let(vd, e, body) if tc.exprHasReturn(e) =>
            val firstType = vd.tpe
            val controlFlowVal =
              ValDef.fresh("cf", ControlFlowSort.controlFlow(retType, firstType)).setPos(e)

            Let(
              controlFlowVal,
              transform(e, firstType),
              ControlFlowSort.andThen(
                retType, firstType, currentType,
                controlFlowVal.toVariable,
                v => replaceFromSymbols(Map(vd -> v), proceedOrTransform(body, currentType)),
                body.getPos
              )
            ).setPos(expr)

          case Let(vd, e, body) =>
            Let(vd, e, transform(body, currentType)).setPos(expr)

          case LetVar(vd, e, body) if tc.exprHasReturn(e) =>
            val firstType = vd.tpe
            val controlFlowVal =
              ValDef.fresh("cf", ControlFlowSort.controlFlow(retType, firstType)).setPos(e)

            LetVar(
              controlFlowVal,
              transform(e, firstType),
              ControlFlowSort.andThen(
                retType, firstType, currentType,
                controlFlowVal.toVariable,
                v => replaceFromSymbols(Map(vd -> v), proceedOrTransform(body, currentType)),
                body.getPos
              )
            ).setPos(expr)

          case LetVar(vd, e, body) =>
            LetVar(vd, e, transform(body, currentType)).setPos(expr)

          case Block(es, last) =>
            def processBlockExpressions(es: Seq[Expr]): Expr = es match {
              case Seq(e) => transform(e, currentType)

              case e +: rest if (tc.exprHasReturn(e)) =>
                val firstType = e.getType
                val controlFlowVal =
                  ValDef.fresh("cf", ControlFlowSort.controlFlow(retType, firstType)).setPos(e)
                val transformedRest = processBlockExpressions(rest)

                if (rest.exists(tc.exprHasReturn)) {
                  Let(
                    controlFlowVal,
                    transform(e, firstType),
                    ControlFlowSort.andThen(
                      retType, firstType, currentType,
                      controlFlowVal.toVariable,
                      _ => transformedRest,
                      rest.head.getPos
                    )
                  ).setPos(e)
                } else {
                  Let(
                    controlFlowVal,
                    transform(e, firstType),
                    ControlFlowSort.andThen(
                      retType, firstType, currentType,
                      controlFlowVal.toVariable,
                      _ => ControlFlowSort.proceed(retType, currentType, transformedRest),
                      rest.head.getPos
                    )
                  ).setPos(e)
                }

              case e +: rest =>
                val unusedVal = ValDef.fresh("unused", e.getType)
                Let(unusedVal, e, processBlockExpressions(rest)).setPos(expr)
            }
            processBlockExpressions(es :+ last)

          case _ =>
            context.reporter.fatalError(expr.getPos,
              s"Keyword `return` is not supported in expression (${expr.getClass}):\n${expr.asString}"
            )
        }
      }

      val newBody =
        if (tc.funHasReturn(fd.id))
          specced.bodyOpt.map { body =>
            val topLevelCF = ValDef.fresh("topLevelCF", ControlFlowSort.controlFlow(retType, retType)).setPos(fd.fullBody)
            Let(topLevelCF, ReturnTransformer.transform(body),
              ControlFlowSort.buildMatch(retType, retType, topLevelCF.toVariable,
                v => v,
                v => v,
                body.getPos
              )
            ).setPos(body)
          }
        else
          specced.bodyOpt.map(ReturnTransformer.transform)

      fd.copy(fullBody = specced.withBody(newBody, retType).reconstructed).setPos(fd)
    }
    else fd
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    if (symbols.functions.values.exists(fd => context.funHasReturn(fd.id)))
      super.extractSymbols(context, symbols)
        .withSorts(Seq(ControlFlowSort.syntheticControlFlow))
    else
      super.extractSymbols(context, symbols)
  }
}

object ReturnElimination {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new ReturnElimination {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
