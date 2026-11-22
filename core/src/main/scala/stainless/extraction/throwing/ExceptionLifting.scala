/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package throwing

import scala.collection.mutable

/** Lifts exceptions into explicit result values.
  *
  * A function whose body carries a `throwing(pred)` clause may throw: its return type `T` becomes
  * the synthetic `Completion[T]`, with the constructors `Normal(value: T)` and
  * `Thrown(exception: Exception)`, after the normal and abrupt completions of the Java language
  * specification. Its postcondition then applies to the normal results, and
  * `pred` to the exceptions it throws.
  *
  * Every other function, lambda and specification may not let an exception escape: a `throw`, or a
  * call to a throwing function, whose exception is not caught becomes an assertion that it is
  * unreachable. This is the semantics that `throw` had before `try` was supported.
  *
  * Inside a function, an exception propagates with a `return` to the end of the enclosing `try`
  * block or function. The body of a `try` that may throw becomes a local function, so that a
  * `return` leaves the block only, and the existing [[imperative.ReturnElimination]] then handles
  * exits from loops and nested expressions. A `return` from the enclosing function inside such a
  * block is carried out by the synthetic `TryCompletion[T, R]` with a third constructor
  * `TryReturned(value: R)`.
  *
  * Within a `try`/`catch`, an exception that no case matches is thrown again, and a `finally` block
  * runs after the body and the handlers, whether they complete normally, throw or return.
  */
class ExceptionLifting(override val s: Trees, override val t: imperative.Trees)
                      (using override val context: inox.Context)
  extends oo.CachingPhase
     with SimpleFunctions
     with IdentitySorts
     with oo.IdentityTypeDefs
     with oo.IdentityClasses
     with oo.NoSummaryPhase { self =>

  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)](
    (fd, context) => getDependencyKey(fd.id)(using context.symbols)
  )

  /** The synthetic sorts used to lift exceptions, for a given `stainless.lang.Exception` class. */
  protected class LiftedSorts(exceptionClass: Identifier) {
    import t.dsl._

    val excType: t.Type = t.ClassType(exceptionClass, Seq())

    private val Seq(completionId, normalId, thrownId) =
      Seq("Completion", "Normal", "Thrown").map(name => ast.SymbolIdentifier("stainless.internal." + name))

    val completionSort: t.ADTSort = mkSort(completionId, t.Synthetic)("T") { case Seq(tT) =>
      Seq(
        (normalId, Seq(t.ValDef(FreshIdentifier("value"), tT))),
        (thrownId, Seq(t.ValDef(FreshIdentifier("exception"), excType)))
      )
    }

    private val Seq(tryCompletionId, tryNormalId, tryThrownId, tryReturnedId) =
      Seq("TryCompletion", "TryNormal", "TryThrown", "TryReturned").map(name => ast.SymbolIdentifier("stainless.internal." + name))

    val tryCompletionSort: t.ADTSort = mkSort(tryCompletionId, t.Synthetic)("T", "R") { case Seq(tT, rT) =>
      Seq(
        (tryNormalId, Seq(t.ValDef(FreshIdentifier("value"), tT))),
        (tryThrownId, Seq(t.ValDef(FreshIdentifier("exception"), excType))),
        (tryReturnedId, Seq(t.ValDef(FreshIdentifier("value"), rT)))
      )
    }

    def sorts: Seq[t.ADTSort] = Seq(completionSort, tryCompletionSort)

    /** How a value of one of the two sorts is built and taken apart. */
    sealed abstract class Shape {
      val tps: Seq[t.Type]
      def tpe: t.Type
      def normal: Identifier
      def thrown: Identifier
      def returned: Option[Identifier]

      def mkNormal(e: t.Expr): t.Expr = t.ADT(normal, tps, Seq(e)).copiedFrom(e)
      def mkThrown(e: t.Expr): t.Expr = t.ADT(thrown, tps, Seq(e)).copiedFrom(e)
      def mkReturned(e: t.Expr): t.Expr = t.ADT(returned.get, tps, Seq(e)).copiedFrom(e)

      def pattern(cons: Identifier, binder: Option[t.ValDef]): t.Pattern =
        t.ADTPattern(None, cons, tps, Seq(t.WildcardPattern(binder)))
    }

    case class CompletionShape(valueType: t.Type) extends Shape {
      val tps = Seq(valueType)
      def tpe = t.ADTType(completionId, tps)
      def normal = normalId
      def thrown = thrownId
      def returned = None
    }

    case class TryCompletionShape(valueType: t.Type, returnType: t.Type) extends Shape {
      val tps = Seq(valueType, returnType)
      def tpe = t.ADTType(tryCompletionId, tps)
      def normal = tryNormalId
      def thrown = tryThrownId
      def returned = Some(tryReturnedId)
    }
  }

  // The sorts are created once per exception class so that their identifiers stay stable.
  private val liftedSortsCache = mutable.Map[Identifier, LiftedSorts]()
  private def liftedSortsFor(exceptionClass: Identifier): LiftedSorts = liftedSortsCache.synchronized {
    liftedSortsCache.getOrElseUpdate(exceptionClass, new LiftedSorts(exceptionClass))
  }

  private def isThrowing(fullBody: s.Expr): Boolean =
    s.exprOps.BodyWithSpecs(fullBody).specs.exists(_.kind == s.exprOps.ExceptionsKind)

  protected class TransformerContext(val symbols: s.Symbols) {
    val liftedSorts: Option[LiftedSorts] =
      symbols.lookup.get[s.ClassDef]("stainless.lang.Exception").map(cd => liftedSortsFor(cd.id))

    val throwingFunctions: Set[Identifier] =
      symbols.functions.values.filter(fd => isThrowing(fd.fullBody)).map(_.id).toSet

    // The sorts are only needed by throwing functions and `try` blocks.
    val needsSorts: Boolean = liftedSorts.isDefined && (throwingFunctions.nonEmpty || symbols.functions.values.exists { fd =>
      s.exprOps.exists { case _: s.Try => true case _ => false }(fd.fullBody)
    })
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  private class IdentityImpl(override val s: self.s.type, override val t: self.t.type)
    extends transformers.ConcreteTreeTransformer(s, t)
  private val identity = new IdentityImpl(self.s, self.t)

  override protected def extractFunction(tc: TransformerContext, fd: s.FunDef): (t.FunDef, Unit) = tc.liftedSorts match {
    case Some(ls) => (new Lifter(tc, ls, fd).result, ())
    case None => (identity.transform(fd), ())
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): (t.Symbols, OOAllSummaries) = {
    val (syms, summaries) = super.extractSymbols(context, symbols)
    if (context.needsSorts) (syms.withSorts(context.liftedSorts.get.sorts), summaries)
    else (syms, summaries)
  }

  /** What an escaping exception and a `return` become at some point of a function body. */
  private case class Escape(
    // How an exception escapes, given the exception, a message for the unreachability assertion, and a position
    raise: (t.Expr, String, inox.utils.Position) => t.Expr,
    // How `return e` from the enclosing function is carried out
    ret: (t.Expr, inox.utils.Position) => t.Expr,
    // The return type of the enclosing function, if `return` may be used here
    returnType: Option[t.Type]
  )

  private class Lifter(tc: TransformerContext, ls: LiftedSorts, fd: s.FunDef) { lifter =>
    import tc.symbols.given
    import ls._

    private class TransformerImpl(override val s: self.s.type, override val t: self.t.type)
      extends transformers.ConcreteTreeTransformer(s, t) {
      override def transform(e: s.Expr): t.Expr = lifter.transform(e)
      def superTransform(e: s.Expr): t.Expr = super.transform(e)
    }
    private val tr = new TransformerImpl(self.s, self.t)

    private def transform(tpe: s.Type): t.Type = tr.transform(tpe)
    private def transform(vd: s.ValDef): t.ValDef = tr.transform(vd)
    private def transform(tpd: s.TypeParameterDef): t.TypeParameterDef = tr.transform(tpd)
    private def transform(flag: s.Flag): t.Flag = tr.transform(flag)
    private def transform(pat: s.Pattern): t.Pattern = tr.transform(pat)

    private def unreachable(msg: String, pos: inox.utils.Position): t.Expr =
      t.Assert(t.BooleanLiteral(false).setPos(pos), Some(msg), t.NoTree(t.NothingType()).setPos(pos)).setPos(pos)

    private val noEscape = Escape(
      (_, msg, pos) => unreachable(msg, pos),
      (e, pos) => t.Return(e).setPos(pos),
      None
    )

    private var escape: Escape = noEscape

    private def withEscape[A](esc: Escape)(body: => A): A = {
      val old = escape
      escape = esc
      try body finally escape = old
    }

    private val throwingLocals: Set[Identifier] = s.exprOps.collect[Identifier] {
      case s.LetRec(lfds, _) => lfds.filter(lfd => isThrowing(lfd.fullBody)).map(_.id).toSet
      case _ => Set()
    } (fd.fullBody)

    private def isThrowingCall(e: s.Expr): Boolean = e match {
      case s.FunctionInvocation(id, _, _) => tc.throwingFunctions(id)
      case s.ApplyLetRec(id, _, _, _, _) => throwingLocals(id)
      case _ => false
    }

    /** Whether evaluating `e` may throw: lambdas and local function definitions are not entered. */
    private def mayThrow(e: s.Expr): Boolean = e match {
      case _: s.Throw => true
      case _ if isThrowingCall(e) => true
      case _: s.Lambda => false
      case s.LetRec(_, body) => mayThrow(body)
      case s.Operator(es, _) => es.exists(mayThrow)
    }

    /** Whether `e` contains a `return` from the enclosing function. */
    private def hasReturn(e: s.Expr): Boolean = e match {
      case _: s.Return => true
      case _: s.Lambda => false
      case s.LetRec(_, body) => hasReturn(body)
      case s.Operator(es, _) => es.exists(hasReturn)
    }

    /** Matches on a value of the given shape, with one handler per constructor. */
    private def matchShape(shape: Shape, scrut: t.Expr, pos: inox.utils.Position)
                          (onNormal: t.Variable => t.Expr, onThrown: t.Variable => t.Expr,
                           onReturned: t.Variable => t.Expr = _ => sys.error("no returned case")): t.Expr = {
      val v = t.ValDef.fresh("v", shape.tps.head).setPos(pos)
      val exc = t.ValDef.fresh("exc", excType).setPos(pos)
      val normalCase = t.MatchCase(shape.pattern(shape.normal, Some(v)), None, onNormal(v.toVariable)).setPos(pos)
      val thrownCase = t.MatchCase(shape.pattern(shape.thrown, Some(exc)), None, onThrown(exc.toVariable)).setPos(pos)
      val returnedCase = shape.returned.map { id =>
        val r = t.ValDef.fresh("r", shape.tps(1)).setPos(pos)
        t.MatchCase(shape.pattern(id, Some(r)), None, onReturned(r.toVariable)).setPos(pos)
      }
      t.MatchExpr(scrut, Seq(normalCase, thrownCase) ++ returnedCase).setPos(pos)
    }

    /** Unwraps the result of a call to a throwing function, letting its exception escape. */
    private def unwrapCall(call: t.Expr, valueType: t.Type, callee: Identifier, pos: inox.utils.Position): t.Expr =
      matchShape(CompletionShape(valueType), call, pos)(
        v => v,
        exc => escape.raise(exc, s"exception thrown by ${callee.asString} unreachable", pos)
      )

    def transform(e: s.Expr): t.Expr = e match {
      case s.Throw(ex) =>
        escape.raise(transform(ex), s"throw $ex unreachable", e.getPos)

      case fi @ s.FunctionInvocation(id, tps, args) if tc.throwingFunctions(id) =>
        val call = t.FunctionInvocation(id, tps.map(transform), args.map(transform)).copiedFrom(e)
        unwrapCall(call, transform(fi.getType), id, e.getPos)

      case alr @ s.ApplyLetRec(id, tparams, tpe, tps, args) if throwingLocals(id) =>
        val newTpe = t.FunctionType(tpe.from.map(transform), CompletionShape(transform(tpe.to)).tpe).copiedFrom(tpe)
        val call = t.ApplyLetRec(
          id, tparams.map(tp => transform(tp).asInstanceOf[t.TypeParameter]), newTpe, tps.map(transform), args.map(transform)
        ).copiedFrom(e)
        unwrapCall(call, transform(alr.getType), id, e.getPos)

      case s.Return(v) =>
        escape.ret(transform(v), e.getPos)

      case tr: s.Try =>
        transformTry(tr)

      case s.LetRec(lfds, body) =>
        t.LetRec(lfds.map(transformLocal), transform(body)).copiedFrom(e)

      case _: s.Lambda | _: s.Forall | _: s.Choose =>
        withEscape(noEscape)(tr.superTransform(e))

      case s.While(cond, body, pred, pred2, flags) =>
        t.While(
          transform(cond),
          transform(body),
          pred.map(p => withEscape(noEscape)(transform(p))),
          pred2.map(p => withEscape(noEscape)(transform(p))),
          flags.map(transform)
        ).copiedFrom(e)

      case s.Throwing(_, _) =>
        throw MalformedStainlessCode(e, "`throwing` clauses are only supported on function bodies")

      case _ =>
        tr.superTransform(e)
    }

    private def transformCase(mc: s.MatchCase): t.MatchCase =
      t.MatchCase(transform(mc.pattern), mc.optGuard.map(transform), transform(mc.rhs)).copiedFrom(mc)

    private def transformTry(tr: s.Try): t.Expr = tr match {
      // `try b catch cs finally f` is `try { try b catch cs } finally f`
      case s.Try(body, cases, Some(fin)) if cases.nonEmpty =>
        transformTry(s.Try(s.Try(body, cases, None).copiedFrom(tr), Seq(), Some(fin)).copiedFrom(tr))

      case s.Try(body, cases, fin) =>
        val pos = tr.getPos
        val valueType = transform(tr.getType)
        if (valueType == t.Untyped)
          throw MalformedStainlessCode(tr, "Could not type the `try` expression")

        if (!mayThrow(body) && (fin.isEmpty || !hasReturn(body))) {
          // The handlers are unreachable, and `finally` runs right after the body
          val newBody = transform(body)
          fin match {
            case None => newBody
            case Some(f) =>
              val res = t.ValDef.fresh("res", valueType).setPos(pos)
              t.Let(res, newBody, t.Block(Seq(transform(f)), res.toVariable).setPos(pos)).setPos(pos)
          }
        } else {
          val outer = escape
          val shape: Shape = outer.returnType match {
            case Some(rt) if hasReturn(body) => TryCompletionShape(valueType, rt)
            case _ => CompletionShape(valueType)
          }

          val bodyEscape = Escape(
            (exc, _, p) => t.Return(shape.mkThrown(exc)).setPos(p),
            shape match {
              case _: TryCompletionShape => (v, p) => t.Return(shape.mkReturned(v)).setPos(p)
              case _ => outer.ret
            },
            outer.returnType
          )

          val newBody = withEscape(bodyEscape)(transform(body))
          // The local function is inlined back at its only call, with the verification conditions of
          // its body: they are then checked with the facts known before the `try`.
          val lfd = t.LocalFunDef(
            FreshIdentifier("tryBlock"), Seq(), Seq(), shape.tpe, shape.mkNormal(newBody), Seq(t.Synthetic, t.Inline)
          ).setPos(pos)
          val call = t.ApplyLetRec(lfd.id, Seq(), t.FunctionType(Seq(), shape.tpe), Seq(), Seq()).setPos(pos)

          def onThrown(exc: t.Variable): t.Expr =
            if (cases.isEmpty) outer.raise(exc, "uncaught exception unreachable", pos)
            else t.MatchExpr(exc, cases.map(transformCase) :+ t.MatchCase(
              t.WildcardPattern(None), None, outer.raise(exc, "uncaught exception unreachable", pos)
            ).setPos(pos)).setPos(pos)

          def dispatch(completion: t.Expr): t.Expr =
            matchShape(shape, completion, pos)(v => v, onThrown, r => outer.ret(r, pos))

          val res = fin match {
            case None => dispatch(call)
            case Some(f) =>
              val completion = t.ValDef.fresh("completion", shape.tpe).setPos(pos)
              t.Let(completion, call, t.Block(Seq(transform(f)), dispatch(completion.toVariable)).setPos(pos)).setPos(pos)
          }
          t.LetRec(Seq(lfd), res).setPos(pos)
        }
    }

    /** Lifts the body of a function, returning its new return type and full body. */
    private def liftBody(returnType: s.Type, fullBody: s.Expr): (t.Type, t.Expr) = {
      val specced = s.exprOps.BodyWithSpecs(fullBody)
      val pred = specced.specs.collectFirst { case s.exprOps.Exceptions(pred) => pred }
      val valueType = transform(returnType)

      pred match {
        case None =>
          val newBody = specced.bodyOpt.map { body =>
            withEscape(Escape((_, msg, pos) => unreachable(msg, pos), (e, pos) => t.Return(e).setPos(pos), Some(valueType))) {
              transform(body)
            }
          }
          val newSpecs = withEscape(noEscape)(specced.specs.map(_.transform(tr)))
          (valueType, t.exprOps.reconstructSpecs(newSpecs, newBody, valueType))

        case Some(pred @ s.Lambda(Seq(excVd), predBody)) =>
          val shape = CompletionShape(valueType)
          val newBody = specced.bodyOpt.map { body =>
            val esc = Escape(
              (exc, _, pos) => t.Return(shape.mkThrown(exc)).setPos(pos),
              (e, pos) => t.Return(shape.mkNormal(e)).setPos(pos),
              Some(valueType)
            )
            shape.mkNormal(withEscape(esc)(transform(body)))
          }

          def liftedPost(post: Option[(s.ValDef, s.Expr)], pos: inox.utils.Position): t.Lambda = {
            val res = t.ValDef.fresh("res", shape.tpe).setPos(pos)
            val (normalBinder, normalBody) = post match {
              case Some((vd, body)) => (Some(transform(vd)), transform(body))
              case None => (None, t.BooleanLiteral(true).setPos(pos))
            }
            t.Lambda(Seq(res), t.MatchExpr(res.toVariable, Seq(
              t.MatchCase(shape.pattern(shape.normal, normalBinder), None, normalBody).setPos(pos),
              t.MatchCase(shape.pattern(shape.thrown, Some(transform(excVd))), None, transform(predBody)).setPos(pos)
            )).setPos(pos)).setPos(pos)
          }

          val otherSpecs = specced.specs.filter(_.kind != s.exprOps.ExceptionsKind)
          val newSpecs = withEscape(noEscape) {
            val lifted = otherSpecs.map {
              case spec @ s.exprOps.Postcondition(s.Lambda(Seq(vd), post)) =>
                t.exprOps.Postcondition(liftedPost(Some((vd, post)), spec.getPos)).setPos(spec)
              case spec => spec.transform(tr)
            }
            if (otherSpecs.exists(_.kind == s.exprOps.PostconditionKind)) lifted
            else lifted :+ t.exprOps.Postcondition(liftedPost(None, pred.getPos)).setPos(pred)
          }
          (shape.tpe, t.exprOps.reconstructSpecs(newSpecs, newBody, shape.tpe))

        case Some(pred) =>
          throw MalformedStainlessCode(pred, "The `throwing` clause must be a predicate on exceptions")
      }
    }

    private def transformLocal(lfd: s.LocalFunDef): t.LocalFunDef = {
      val (newReturnType, newBody) = liftBody(lfd.returnType, lfd.fullBody)
      t.LocalFunDef(
        lfd.id, lfd.tparams.map(transform), lfd.params.map(transform), newReturnType, newBody, lfd.flags.map(transform)
      ).copiedFrom(lfd)
    }

    lazy val result: t.FunDef = {
      val (newReturnType, newBody) = liftBody(fd.returnType, fd.fullBody)
      new t.FunDef(
        fd.id, fd.tparams.map(transform), fd.params.map(transform), newReturnType, newBody, fd.flags.map(transform)
      ).copiedFrom(fd)
    }
  }
}

object ExceptionLifting {
  def apply(ts: Trees, tt: imperative.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends ExceptionLifting(s, t)
    new Impl(ts, tt)
  }
}
