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
  }

  /* Extract functional result value. Useful to remove side effect from conditions when moving it to post-condition */
  def getFunctionalResult(expr: t.Expr): t.Expr = t.exprOps.postMap {
    case t.Block(_, res) => Some(res)
    case _ => None
  }(expr)

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  object NoReturnCheck extends transformers.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    def transform(lfd: s.LocalFunDef): t.LocalFunDef = {
      val s.LocalFunDef(id, tparams, params, retType, fullBody, flags) = lfd
      t.LocalFunDef(
        id,
        tparams.map(transform),
        params.map(transform),
        transform(retType),
        transform(fullBody),
        flags.map(transform)
      ).setPos(lfd)
    }

    override def transform(e: s.Expr): t.Expr = e match {
      case s.Return(_) =>
        context.reporter.fatalError(e.getPos, "Keyword `return` is not allowed here")
      case _ => super.transform(e)
    }
  }

  protected def extractFunction(tc: TransformerContext, fd: s.FunDef): t.FunDef = {
    implicit val symboms = tc.symbols

    if (tc.funHasReturn(fd.id)) {
      val specced = s.exprOps.BodyWithSpecs(fd.fullBody)
      val retType = fd.returnType
      val retTypeChecked = NoReturnCheck.transform(retType)
      val topLevelPost = specced.getSpec(s.exprOps.PostconditionKind)

      object ReturnTransformer extends TransformerWithType {
        override val s: self.s.type = self.s
        override val t: self.t.type = self.t
        override val symbols: s.Symbols = tc.symbols

        private def proceedOrTransform(expr: s.Expr, currentType: s.Type): t.Expr = {
          val currentTypeChecked = NoReturnCheck.transform(currentType)
          if (tc.exprHasReturn(expr)) transform(expr, currentType)
          else ControlFlowSort.proceed(retTypeChecked, currentTypeChecked, NoReturnCheck.transform(expr))
        }

        private def proceedOrTransform(mc: s.MatchCase, currentType: s.Type): t.MatchCase = {
          val s.MatchCase(pattern, optGuard, rhs) = mc
          t.MatchCase(
            NoReturnCheck.transform(pattern),
            optGuard.map(NoReturnCheck.transform),
            proceedOrTransform(rhs, currentType)
          ).setPos(mc)
        }

        override def transform(expr: s.Expr, currentType: s.Type): t.Expr = expr match {
          case wh @ s.While(cond, body, optInv)
            if !tc.exprHasReturn(cond) && optInv.forall(inv => !tc.exprHasReturn(inv)) =>

            assert(tc.exprHasReturn(body),
              "While loops without `return` must transformed in the `SimpleWhileElimination` phase"
            )

            val id = FreshIdentifier(fd.id.name + "While")
            val loopType = ControlFlowSort.controlFlow(NoReturnCheck.transform(retType), t.UnitType())
            val tpe = t.FunctionType(Seq(), loopType.copiedFrom(wh)).copiedFrom(wh)

            val specced = s.exprOps.BodyWithSpecs(body)
            val measure = specced.getSpec(s.exprOps.MeasureKind).map(spec =>
              NoReturnCheck.transform(spec.expr)
            )

            val ite =
              t.IfExpr(
                NoReturnCheck.transform(cond),
                t.ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
                ControlFlowSort.proceed(retTypeChecked, t.UnitType(), t.UnitLiteral()).copiedFrom(wh)
              ).copiedFrom(wh)

            val newBody =
              ControlFlowSort.andThen(retTypeChecked, t.UnitType(), t.UnitType(),
                transform(specced.body, s.UnitType()),
                _ => ite,
                wh.getPos
              )

            val optInvChecked = optInv.map(NoReturnCheck.transform)
            val condChecked = NoReturnCheck.transform(cond)


            val cfWhileVal = t.ValDef.fresh("cfWhile", loopType.copiedFrom(wh)).copiedFrom(wh)
            val newPost =
              t.Lambda(
                Seq(cfWhileVal),
                ControlFlowSort.buildMatch(retTypeChecked, t.UnitType(), cfWhileVal.toVariable,
                  // when the while loop returns, we check that the while loop invariant and the
                  // postcondition of the top-level function hold
                  v => t.and(
                    topLevelPost.map { case s.exprOps.Postcondition(s.Lambda(Seq(postVd), postBody)) =>
                      t.exprOps.replaceFromSymbols(
                        Map(NoReturnCheck.transform(postVd) -> v),
                        NoReturnCheck.transform(postBody)
                      )(t.convertToVal)
                    }.getOrElse(t.BooleanLiteral(true)),
                    optInvChecked.getOrElse(t.BooleanLiteral(true).copiedFrom(wh)),
                  ),
                  // when the while loop terminates without returning, we check the loop condition
                  // is false and that the invariant is true
                  _ => t.and(
                    t.Not(getFunctionalResult(condChecked).copiedFrom(cond)).copiedFrom(cond),
                    optInvChecked.getOrElse(t.BooleanLiteral(true).copiedFrom(wh))
                  ),
                  wh.getPos
                )
              ).copiedFrom(wh)

            val fullBody = t.exprOps.withPostcondition(
              t.exprOps.withPrecondition(
                t.exprOps.withMeasure(newBody, measure).copiedFrom(wh),
                Some(t.andJoin(optInvChecked.toSeq :+ getFunctionalResult(condChecked)))
              ).copiedFrom(wh),
              Some(newPost)
            ).copiedFrom(wh)

            t.LetRec(
              Seq(t.LocalFunDef(id, Seq(), Seq(), loopType.copiedFrom(wh), fullBody, Seq()).copiedFrom(wh)),
              t.IfExpr(
                condChecked,
                t.ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
                ControlFlowSort.proceed(retTypeChecked, t.UnitType(), t.UnitLiteral()).copiedFrom(wh)
              ).copiedFrom(wh)
            ).copiedFrom(wh)

          case _ if !tc.exprHasReturn(expr) => NoReturnCheck.transform(expr)

          case s.Assert(e, err, rest) if !tc.exprHasReturn(e) =>
            t.Assert(NoReturnCheck.transform(e), err, transform(rest, currentType)).setPos(expr)

          case s.Assume(e, rest) if !tc.exprHasReturn(e) =>
            t.Assume(NoReturnCheck.transform(e), transform(rest, currentType)).setPos(expr)

          case s.Return(e) if !tc.exprHasReturn(e) =>
            ControlFlowSort.ret(
              retTypeChecked,
              NoReturnCheck.transform(currentType),
              NoReturnCheck.transform(e)
            )

          case s.IfExpr(cond, e1, e2) if !tc.exprHasReturn(cond) =>
            t.IfExpr(NoReturnCheck.transform(cond),
              proceedOrTransform(e1, currentType),
              proceedOrTransform(e2, currentType)
            ).setPos(expr)

          case s.MatchExpr(scrut, cases) if !tc.exprHasReturn(scrut) =>
            t.MatchExpr(NoReturnCheck.transform(scrut),
              cases.map(proceedOrTransform(_, currentType))
            ).setPos(expr)

          case s.Let(vd, e, body) if tc.exprHasReturn(e) =>
            val firstType = vd.tpe
            val firstTypeChecked = NoReturnCheck.transform(firstType)
            val controlFlowVal =
              t.ValDef.fresh("cf",
                ControlFlowSort.controlFlow(retTypeChecked, firstTypeChecked)
              ).setPos(e)
            val vdChecked: t.ValDef = NoReturnCheck.transform(vd)

            t.Let(
              controlFlowVal,
              transform(e, firstType),
              ControlFlowSort.andThen(
                retTypeChecked, firstTypeChecked, NoReturnCheck.transform(currentType),
                controlFlowVal.toVariable,
                (v: t.Variable) =>
                  t.exprOps.replaceFromSymbols(
                    Map(vdChecked -> v),
                    proceedOrTransform(body, currentType)
                  )(t.convertToVal),
                body.getPos
              )
            ).setPos(expr)

          case s.Let(vd, e, body) =>
            t.Let(
              NoReturnCheck.transform(vd),
              NoReturnCheck.transform(e),
              transform(body, currentType)
            ).setPos(expr)

          case s.LetVar(vd, e, body) if tc.exprHasReturn(e) =>
            val firstType = vd.tpe
            val firstTypeChecked = NoReturnCheck.transform(firstType)
            val controlFlowVal =
              t.ValDef.fresh("cf",
                ControlFlowSort.controlFlow(retTypeChecked, firstTypeChecked)
              ).setPos(e)
            val vdChecked: t.ValDef = NoReturnCheck.transform(vd)

            t.LetVar(
              controlFlowVal,
              transform(e, firstType),
              ControlFlowSort.andThen(
                retTypeChecked, firstTypeChecked, NoReturnCheck.transform(currentType),
                controlFlowVal.toVariable,
                (v: t.Variable) =>
                  t.exprOps.replaceFromSymbols(
                    Map(vdChecked -> v),
                    proceedOrTransform(body, currentType)
                  )(t.convertToVal),
                body.getPos
              )
            ).setPos(expr)

          case s.LetVar(vd, e, body) =>
            t.LetVar(
              NoReturnCheck.transform(vd),
              NoReturnCheck.transform(e),
              transform(body, currentType)
            ).setPos(expr)

          case s.LetRec(fds, rest) => 
            t.LetRec(fds.map(NoReturnCheck.transform), transform(rest, currentType)).setPos(expr)

          case s.Block(es, last) =>
            val currentTypeChecked = NoReturnCheck.transform(currentType)

            def processBlockExpressions(es: Seq[s.Expr]): t.Expr = es match {
              case Seq(e) => transform(e, currentType)

              case e +: rest if tc.exprHasReturn(e) =>
                val firstType = e.getType
                val firstTypeChecked = NoReturnCheck.transform(e.getType)
                val controlFlowVal =
                  t.ValDef.fresh("cf",
                    ControlFlowSort.controlFlow(retTypeChecked, firstTypeChecked)
                  ).setPos(e)
                val transformedRest = processBlockExpressions(rest)

                t.Let(
                  controlFlowVal,
                  transform(e, firstType),
                  ControlFlowSort.andThen(
                    retTypeChecked, firstTypeChecked, currentTypeChecked,
                    controlFlowVal.toVariable,
                    _ => if (rest.exists(tc.exprHasReturn))
                        transformedRest
                      else
                        ControlFlowSort.proceed(retTypeChecked, currentTypeChecked, transformedRest),
                    rest.head.getPos
                  )
                ).setPos(e)

              case es =>
                val nonReturnEs = es.takeWhile(e => !tc.exprHasReturn(e)).map(NoReturnCheck.transform)
                val others = es.drop(nonReturnEs.size)
                if (others.isEmpty)
                  t.Block(nonReturnEs.init, nonReturnEs.last).copiedFrom(expr)
                else
                  t.Block(nonReturnEs, processBlockExpressions(others)).copiedFrom(expr)
            }
            processBlockExpressions(es :+ last)

          case _ =>
            context.reporter.fatalError(expr.getPos,
              s"Keyword `return` is not supported in expression (${expr.getClass}):\n${expr.asString}"
            )
        }
      }

      // when cf: ControlFlow[A, A]
      // optimisation for `cf match { case Return(retValue) => retValue case Proceed(value) => value }`
      def unwrap(expr: t.Expr): t.Expr = expr match {
        case ControlFlowSort.Return(e) => e
        case ControlFlowSort.Proceed(e) => e
        case t.Let(vd, e, body) => t.Let(vd, e, unwrap(body)).setPos(expr)
        case t.LetVar(vd, e, body) => t.LetVar(vd, e, unwrap(body)).setPos(expr)
        case t.LetRec(fds, rest) => t.LetRec(fds, unwrap(rest)).setPos(expr)
        case t.Assert(cond, err, body) => t.Assert(cond, err, unwrap(body)).setPos(expr)
        case t.Assume(cond, body) => t.Assume(cond, unwrap(body)).setPos(expr)
        case t.IfExpr(cond, e1, e2) => t.IfExpr(cond, unwrap(e1), unwrap(e2)).setPos(expr)
        case t.MatchExpr(scrut, cases) => t.MatchExpr(scrut, cases.map {
          case mc @ t.MatchCase(pat, optGuard, rhs) =>
          t.MatchCase(pat, optGuard, unwrap(rhs)).copiedFrom(mc)
        }).setPos(expr)
        case t.Block(es, last) => t.Block(es, unwrap(last)).setPos(expr)
        case _ => expr
      }

      val newBody =
        if (tc.funHasReturn(fd.id))
          specced.bodyOpt.map { body =>
            unwrap(ReturnTransformer.transform(body, retType)).setPos(body)
          }
        else
          specced.bodyOpt.map(ReturnTransformer.transform)

      val newBodyWithSpecs = t.exprOps.BodyWithSpecs(
        specced.lets.map {
          case (vd0, e0, pos0) =>
            (NoReturnCheck.transform(vd0), NoReturnCheck.transform(e0), pos0)
        },
        specced.specs.map(spec => spec.map(t)(NoReturnCheck.transform)),
        t.UnitLiteral() // replaced with the `withBody` call below
      ).withBody(newBody, retTypeChecked).reconstructed


      new t.FunDef(
        fd.id,
        fd.tparams.map(NoReturnCheck.transform),
        fd.params.map(NoReturnCheck.transform),
        NoReturnCheck.transform(fd.returnType),
        newBodyWithSpecs,
        fd.flags.map(NoReturnCheck.transform)
      ).setPos(fd)
    }
    else
      NoReturnCheck.transform(fd)
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
