/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

class ReturnElimination(override val s: Trees, override val t: Trees)
                       (using override val context: inox.Context)
  extends oo.CachingPhase
     with IdentitySorts
     with SimplyCachedFunctions
     with SimpleFunctions
     with oo.IdentityTypeDefs
     with oo.IdentityClasses
     with utils.SyntheticSorts { self =>

  given givenSPrinterOpts: s.PrinterOptions = s.PrinterOptions.fromContext(context)
  given givenTPrinterOpts: t.PrinterOptions = t.PrinterOptions.fromContext(context)

  protected class TransformerContext(val symbols: s.Symbols) {
    private val deconstructor = s.getDeconstructor(t)

    // the set of expressions containing a return expression
    val exprHasReturn = collection.mutable.Map[Identifier, collection.mutable.Set[s.Expr]]()

    def addExpression(id: Identifier, e: s.Expr): Unit = {
      if (exprHasReturn.contains(id))
        exprHasReturn(id) += e
      else
        exprHasReturn(id) = collection.mutable.Set(e)
    }

    class ReturnFinder(override val trees: self.s.type) extends transformers.Traverser {
      // holds the identifier of the current LocalFunDef
      // initially equal to the top-level `fid`
      type Env = Identifier

      override def traverse(expr: s.Expr, currentId: Env): Unit = expr match {
        case s.LetRec(lfds, rest) =>
          lfds.foreach(lfd => traverse(lfd.fullBody, lfd.id))
          traverse(rest, currentId)
          if (exprHasReturn.contains(currentId) && exprHasReturn(currentId)(rest))
            addExpression(currentId, expr)

        case s.Return(e) =>
          addExpression(currentId, expr)

        case s.Operator(es, _) =>
          super.traverse(expr, currentId)

          if (exprHasReturn.contains(currentId) && es.exists(exprHasReturn(currentId)))
            addExpression(currentId, expr)
      }
    }

    val returnFinder = new ReturnFinder(self.s)
    for (fd <- symbols.functions.values) returnFinder.traverse(fd.fullBody, fd.id)
  }

  /* Extract functional result value. Useful to remove side effect from conditions when moving it to post-condition */
  def getFunctionalResult(expr: t.Expr): t.Expr = t.exprOps.postMap {
    case t.Block(_, res) => Some(res)
    case _ => None
  }(expr)

  // when expr: ControlFlow[retT, retT]
  // optimisation for `expr match { case Return(retValue) => retValue case Proceed(value) => value }`
  def unwrap(expr: t.Expr, retT: t.Type): t.Expr = {
    def rec(expr: t.Expr): t.Expr = expr match {
      case ControlFlowSort.Return(e) => e
      case ControlFlowSort.Proceed(e) => e
      case t.Let(vd, e, body) => t.Let(vd, e, rec(body)).setPos(expr)
      case t.LetVar(vd, e, body) => t.LetVar(vd, e, rec(body)).setPos(expr)
      case t.LetRec(fds, rest) => t.LetRec(fds, rec(rest)).setPos(expr)
      case t.Assert(cond, err, body) => t.Assert(cond, err, rec(body)).setPos(expr)
      case t.Assume(cond, body) => t.Assume(cond, rec(body)).setPos(expr)
      case t.IfExpr(cond, e1, e2) => t.IfExpr(cond, rec(e1), rec(e2)).setPos(expr)
      case t.MatchExpr(scrut, cases) => t.MatchExpr(scrut, cases.map {
        case mc @ t.MatchCase(pat, optGuard, rhs) =>
        t.MatchCase(pat, optGuard, rec(rhs)).copiedFrom(mc)
      }).setPos(expr)
      case t.Block(es, last) => t.Block(es, rec(last)).setPos(expr)
      case _ =>
        ControlFlowSort.buildMatch(retT, retT, expr,
          res => res,
          res => res,
          expr.getPos
        )
    }
    rec(expr)
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected def extractFunction(tc: TransformerContext, fd: s.FunDef): t.FunDef = {
    import tc.symbols.given

    class SimpleWhileTransformer(override val s: self.s.type, override val t: self.t.type)
      extends transformers.ConcreteTreeTransformer(s, t) { transSelf =>

      override def transform(e: s.Expr): t.Expr = e match {
        // we allow `return` inside local function definitions
        case s.LetRec(lfds, rest) =>
          t.LetRec(
            lfds.map(lfd => new ReturnTransformer(this, s.Inner(lfd)).getResult.asInstanceOf[t.Inner].fd),
            transform(rest)
          ).setPos(e)

        case s.Return(_) =>
          context.reporter.fatalError(e.getPos, "Keyword `return` is not allowed here")

        case wh @ s.While(cond, body, optInv, optWeakInv, flags) =>
          val transformedCond = transform(cond)
          val transformedBody = transform(body)
          val transformedInv = optInv.map(transform)

          if (optWeakInv.nonEmpty) {
            context.reporter.fatalError(
              "In ReturnElimination Phase, unexpected `noReturnInvariant` for a while loop without return"
            )
          }

          val id = FreshIdentifier(fd.id.name + "While")
          val tpe = t.FunctionType(Seq(), t.UnitType().copiedFrom(wh)).copiedFrom(wh)

          val specced = t.exprOps.BodyWithSpecs(transformedBody)

          val ite =
            t.IfExpr(
              transformedCond,
              t.ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
              t.UnitLiteral().copiedFrom(wh)
            ).copiedFrom(wh)

          val newBody = specced.bodyOpt.map { body =>
            t.Block(
              Seq(body),
              ite
            ).copiedFrom(wh)
          }

          val newPost =
            t.Lambda(
              Seq(t.ValDef.fresh("_res", t.UnitType().copiedFrom(wh)).copiedFrom(wh)),
              t.SplitAnd.many(
                transformedInv.getOrElse(t.BooleanLiteral(true).copiedFrom(wh)),
                t.Not(getFunctionalResult(transformedCond).copiedFrom(cond)).copiedFrom(cond),
              ).copiedFrom(wh)
            ).copiedFrom(wh)

          assert(!specced.specs.exists(_.kind == t.exprOps.PreconditionKind), "While loops cannot have `require`")
          assert(!specced.specs.exists(_.kind == t.exprOps.PostconditionKind), "While loops cannot have `ensuring`")

          val newSpecs =
            t.exprOps.Postcondition(newPost) +:
            t.exprOps.Precondition(t.SplitAnd.manyJoin(transformedInv.toSeq :+ getFunctionalResult(transformedCond))).setPos(wh) +:
            specced.specs

          val fullBody = t.exprOps.BodyWithSpecs(newSpecs, newBody.getOrElse(t.UnitLiteral())).reconstructed.copiedFrom(wh)

          t.LetRec(
            Seq(t.LocalFunDef(id, Seq(), Seq(), t.UnitType().copiedFrom(wh), fullBody, flags.map(transform)).copiedFrom(wh)),
            t.IfExpr(
              transformedCond,
              t.ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
              t.UnitLiteral().copiedFrom(wh)
            ).copiedFrom(wh)
          ).copiedFrom(wh)

        case s.Block(es, last) =>
          super.transform(e)

        case _ => super.transform(e)
      }
    }


    class ReturnTransformer(override val s: self.s.type,
                            override val t: self.t.type,
                            val simpleWhileTransformer: SimpleWhileTransformer,
                            val fa: s.FunAbstraction)
                           (using override val symbols: self.s.Symbols)
      extends TransformerWithType {

      def this(simpleWhileTransformer: SimpleWhileTransformer, fa: self.s.FunAbstraction) =
        this(self.s, self.t, simpleWhileTransformer, fa)(using tc.symbols)

      def exprHasReturn(e: s.Expr): Boolean =
        tc.exprHasReturn.contains(fa.id) &&
        tc.exprHasReturn(fa.id)(e)

      val specced = s.exprOps.BodyWithSpecs(fa.fullBody)
      val retType = fa.returnType
      val retTypeChecked = simpleWhileTransformer.transform(retType)
      val topLevelPost = specced.getSpec(s.exprOps.PostconditionKind)

      def getResult: t.FunAbstraction = {
        val newBody =
          specced.bodyOpt.map { body =>
            if (tc.exprHasReturn.contains(fa.id))
              unwrap(transform(body, retType), retTypeChecked).setPos(body)
            else
              transform(body, retType)
          }

        val newBodyWithSpecs = t.exprOps.BodyWithSpecs(
          specced.specs.map(_.transform(simpleWhileTransformer)),
          t.UnitLiteral() // replaced with the `withBody` call below
        ).withBody(newBody, retTypeChecked).reconstructed

        fa.to(t)(
          fa.id,
          fa.tparams.map(simpleWhileTransformer.transform),
          fa.params.map(simpleWhileTransformer.transform),
          simpleWhileTransformer.transform(fa.returnType),
          newBodyWithSpecs,
          fa.flags.map(simpleWhileTransformer.transform)
        )
      }

      private def proceedOrTransform(expr: s.Expr, currentType: s.Type): t.Expr = {
        val currentTypeChecked = simpleWhileTransformer.transform(currentType)
        if (exprHasReturn(expr)) transform(expr, currentType)
        else ControlFlowSort.proceed(retTypeChecked, currentTypeChecked, simpleWhileTransformer.transform(expr))
      }

      private def proceedOrTransform(mc: s.MatchCase, currentType: s.Type): t.MatchCase = {
        val s.MatchCase(pattern, optGuard, rhs) = mc
        t.MatchCase(
          simpleWhileTransformer.transform(pattern),
          optGuard.map(simpleWhileTransformer.transform),
          proceedOrTransform(rhs, currentType)
        ).setPos(mc)
      }

      override def transform(expr: s.Expr, currentType: s.Type): t.Expr = expr match {
        case wh @ s.While(cond, body, optInv, optWeakInv, flags) if exprHasReturn(expr) =>

          val id = FreshIdentifier(fd.id.name + "While")
          val loopType = ControlFlowSort.controlFlow(simpleWhileTransformer.transform(retType), t.UnitType())
          val tpe = t.FunctionType(Seq(), loopType.copiedFrom(wh)).copiedFrom(wh)

          val specced = s.exprOps.BodyWithSpecs(body)

          val ite =
            t.IfExpr(
              simpleWhileTransformer.transform(cond),
              t.ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
              ControlFlowSort.proceed(retTypeChecked, t.UnitType(), t.UnitLiteral()).copiedFrom(wh)
            ).copiedFrom(wh)

          val newBody = specced.bodyOpt.map { body =>
            ControlFlowSort.andThen(retTypeChecked, t.UnitType(), t.UnitType(),
              transform(body, s.UnitType()),
              _ => ite,
              wh.getPos
            )
          }

          val optInvChecked = optInv.map(simpleWhileTransformer.transform)
          val optWeakInvChecked = optWeakInv.map(simpleWhileTransformer.transform)
          val condChecked = simpleWhileTransformer.transform(cond)

          val cfWhileVal = t.ValDef.fresh("cfWhile", loopType.copiedFrom(wh)).copiedFrom(wh)
          val newPost =
            t.Lambda(
              Seq(cfWhileVal),
              ControlFlowSort.buildMatch(retTypeChecked, t.UnitType(), cfWhileVal.toVariable,
                // when the while loop returns, we check that the while loop invariant and the
                // postcondition of the top-level function hold
                v => t.SplitAnd.many(
                  optInvChecked.getOrElse(t.BooleanLiteral(true).copiedFrom(wh)),
                  topLevelPost.map { case s.exprOps.Postcondition(s.Lambda(Seq(postVd), postBody)) =>
                    t.exprOps.replaceFromSymbols(
                      Map(simpleWhileTransformer.transform(postVd) -> v),
                      simpleWhileTransformer.transform(postBody)
                    )(using t.convertToVal)
                  }.getOrElse(t.BooleanLiteral(true)),
                ),
                // when the while loop terminates without returning, we check the loop condition
                // is false and that the invariant and weak invariant are true
                _ => t.SplitAnd.many(
                  optInvChecked.getOrElse(t.BooleanLiteral(true).copiedFrom(wh)),
                  optWeakInvChecked.getOrElse(t.BooleanLiteral(true).copiedFrom(wh)),
                  t.Not(getFunctionalResult(condChecked).copiedFrom(cond)).copiedFrom(cond),
                ),
                wh.getPos
              )
            ).copiedFrom(wh)

          val newSpecs =
            t.exprOps.Postcondition(newPost) +:
            t.exprOps.Precondition(t.SplitAnd.manyJoin((optInvChecked.toSeq ++ optWeakInvChecked) :+ getFunctionalResult(condChecked))).setPos(wh) +:
            specced.specs.map(_.transform(simpleWhileTransformer))

          val fullBody = t.exprOps.BodyWithSpecs(newSpecs, newBody.getOrElse(t.UnitLiteral())).reconstructed.copiedFrom(wh)
          val flagsChecked = flags.map(simpleWhileTransformer.transform)

          t.LetRec(
            Seq(t.LocalFunDef(id, Seq(), Seq(), loopType.copiedFrom(wh), fullBody, flagsChecked).copiedFrom(wh)),
            t.IfExpr(
              condChecked,
              t.ApplyLetRec(id, Seq(), tpe, Seq(), Seq()).copiedFrom(wh),
              ControlFlowSort.proceed(retTypeChecked, t.UnitType(), t.UnitLiteral()).copiedFrom(wh)
            ).copiedFrom(wh)
          ).copiedFrom(wh)

        case s.Assert(e, err, rest) =>
          t.Assert(simpleWhileTransformer.transform(e), err, transform(rest, currentType)).setPos(expr)

        case s.Assume(e, rest) =>
          t.Assume(simpleWhileTransformer.transform(e), transform(rest, currentType)).setPos(expr)

        case s.Return(e) =>
          ControlFlowSort.ret(
            retTypeChecked,
            simpleWhileTransformer.transform(currentType),
            simpleWhileTransformer.transform(e)
          )

        case s.IfExpr(cond, e1, e2) if exprHasReturn(expr) =>
          t.IfExpr(simpleWhileTransformer.transform(cond),
            proceedOrTransform(e1, currentType),
            proceedOrTransform(e2, currentType)
          ).setPos(expr)

        case s.MatchExpr(scrut, cases) if exprHasReturn(expr) =>
          t.MatchExpr(simpleWhileTransformer.transform(scrut),
            cases.map(proceedOrTransform(_, currentType))
          ).setPos(expr)

        case s.Let(vd, e, body) if exprHasReturn(e) =>
          val firstType = vd.tpe
          val firstTypeChecked = simpleWhileTransformer.transform(firstType)
          val controlFlowVal =
            t.ValDef.fresh("cf",
              ControlFlowSort.controlFlow(retTypeChecked, firstTypeChecked)
            ).setPos(e)
          val vdChecked: t.ValDef = simpleWhileTransformer.transform(vd)

          t.Let(
            controlFlowVal,
            transform(e, firstType),
            ControlFlowSort.andThen(
              retTypeChecked, firstTypeChecked, simpleWhileTransformer.transform(currentType),
              controlFlowVal.toVariable,
              (v: t.Variable) =>
                t.exprOps.replaceFromSymbols(
                  Map(vdChecked -> v),
                  proceedOrTransform(body, currentType)
                )(using t.convertToVal),
              body.getPos
            )
          ).setPos(expr)

        case s.Let(vd, e, body) => super.transform(expr, currentType)

        case s.LetVar(vd, e, body) if exprHasReturn(e) =>
          val firstType = vd.tpe
          val firstTypeChecked = simpleWhileTransformer.transform(firstType)
          val controlFlowVal =
            t.ValDef.fresh("cf",
              ControlFlowSort.controlFlow(retTypeChecked, firstTypeChecked)
            ).setPos(e)
          val vdChecked: t.ValDef = simpleWhileTransformer.transform(vd)

          t.LetVar(
            controlFlowVal,
            transform(e, firstType),
            ControlFlowSort.andThen(
              retTypeChecked, firstTypeChecked, simpleWhileTransformer.transform(currentType),
              controlFlowVal.toVariable,
              (v: t.Variable) =>
                t.exprOps.replaceFromSymbols(
                  Map(vdChecked -> v),
                  proceedOrTransform(body, currentType)
                )(using t.convertToVal),
              body.getPos
            )
          ).setPos(expr)

        case s.LetVar(vd, e, body) => super.transform(expr, currentType)

        case s.LetRec(lfds, rest) =>
          t.LetRec(
            lfds.map(lfd => new ReturnTransformer(simpleWhileTransformer, s.Inner(lfd)).getResult.asInstanceOf[t.Inner].fd),
            transform(rest, currentType)
          ).setPos(expr)

        case s.Block(es, last) =>
          val currentTypeChecked = simpleWhileTransformer.transform(currentType)

          def processBlockExpressions(es: Seq[s.Expr]): t.Expr = es match {
            case Seq(e) => transform(e, currentType)

            case e +: rest if exprHasReturn(e) =>
              val firstType = e.getType
              val firstTypeChecked = simpleWhileTransformer.transform(e.getType)
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
                  _ => if (rest.exists(exprHasReturn))
                      transformedRest
                    else
                      ControlFlowSort.proceed(retTypeChecked, currentTypeChecked, transformedRest),
                  rest.head.getPos
                )
              ).setPos(e)

            case es =>
              val (nonReturnEs, others) = es.span(e => !exprHasReturn(e))
              val nonReturnsEsChecked = nonReturnEs.map(simpleWhileTransformer.transform(_))
              if (others.isEmpty)
                t.Block(nonReturnsEsChecked.init, nonReturnsEsChecked.last).copiedFrom(expr)
              else
                t.Block(nonReturnsEsChecked, processBlockExpressions(others)).copiedFrom(expr)
          }
          processBlockExpressions(es :+ last)

        case (_: s.Lambda | _: s.Forall | _: s.Old | _: s.Snapshot | _: s.FreshCopy | _: s.Choose) =>
          simpleWhileTransformer.transform(expr)

        case _ if exprHasReturn(expr) =>
          val (ids, vs, es, tps, flags, recons) = deconstructor.deconstruct(expr)
          val tvs = vs.map(simpleWhileTransformer.transform).map(_.asInstanceOf[t.Variable])
          val ttps = tps.map(simpleWhileTransformer.transform)
          val tflags = flags.map(simpleWhileTransformer.transform)

          val currentTypeChecked = simpleWhileTransformer.transform(currentType)

          def rec(es: Seq[s.Expr], tes: Seq[t.Expr]): t.Expr = es match {
            case Seq() => recons(ids, tvs, tes, ttps, tflags)
            case e +: rest if !exprHasReturn(e) =>
              // We use a let-binding here to preserve execution order.
              val vd = t.ValDef.fresh("x", simpleWhileTransformer.transform(e.getType), true).copiedFrom(e)
              t.Let(vd, simpleWhileTransformer.transform(e), rec(rest, tes :+ vd.toVariable)).copiedFrom(e)
            case e +: rest =>
              val firstType = simpleWhileTransformer.transform(e.getType)
              ControlFlowSort.andThen(
                retTypeChecked, firstType, currentTypeChecked,
                transform(e, e.getType),
                (v: t.Variable) => {
                  val transformedRest = rec(rest, tes :+ v)
                  if (rest.exists(exprHasReturn))
                    transformedRest
                  else
                    ControlFlowSort.proceed(retTypeChecked, currentTypeChecked, transformedRest)
                },
                e.getPos
              )
          }

          rec(es, Seq.empty)

        case _ => simpleWhileTransformer.transform(expr)
      }
    }

    val simpleWhileTransformer = new SimpleWhileTransformer(self.s, self.t)
    new ReturnTransformer(simpleWhileTransformer, s.Outer(fd)).getResult.asInstanceOf[t.Outer].fd
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    if (context.exprHasReturn.nonEmpty)
      super.extractSymbols(context, symbols)
        .withSorts(Seq(ControlFlowSort.syntheticControlFlow))
    else
      super.extractSymbols(context, symbols)
  }
}

object ReturnElimination {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends ReturnElimination(s, t)
    new Impl(trees, trees)
  }
}
