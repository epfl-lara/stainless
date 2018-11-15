/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

/** Provides effect analysis for full Stainless language
  *
  * This holds state for caching the current state of the analysis, so if
  * you modify your program you may want to create a new EffectsAnalysis
  * instance.
  *
  * You can use it lazily by only querying effects for the functions you need.
  * The internals make sure to compute only the part of the dependencies graph
  * that is needed to get the effect of the function.
  *
  * An effect is defined as the impact that a function can have on its environment.
  * In the Stainless language, there are no global variables that aren't explicit, so
  * the effect of a function is defined as the set of its parameters that are mutated
  * by executing the body. It is a conservative over-abstraction, as some update operations
  * might actually not modify the object, but this will still be considered as an
  * effect.
  *
  * There are actually a very limited number of features that rely on global state (epsilon).
  * EffectsAnalysis will not take such effects into account. You need to make sure the
  * program either does not rely on epsilon, or has been rewriting with the IntroduceGlobalStatePhase
  * phase that introduce any global state explicitly as function parameters. In the future,
  * if we do end up supporting global variables, it is likely that we will rely on another
  * phase to introduce that global state explicitly into the list of parameters of functions
  * that make use of it.
  *
  * An effect is detected by a FieldAssignment to one of the parameters that are mutable. It
  * can come from transitively calling a function that perform a field assignment as well.
  * If the function uses higher-order functions that take mutable types as parameters, they
  * will be conservatively assumed to perform an effect as well. A function type is not by itself
  * a mutable type, but if it is applied on a mutable type that is taken as a parameter as well,
  * it will be detected as an effect by the EffectsAnalysis.
  * TODO: maybe we could have "conditional effects", effects depending on the effects of the lambda.
  *
  * The EffectsAnalysis also provides functions to analyze the the mutability of a type and expression.
  * The isMutableType function needs to perform a graph traversal (explore all the fields recursively
  * to find if one is mutable)
  *
  * Throughout the code, we assume that there is no aliasing. This is the global assumption made
  * in Stainless for effects. Some alias analysis to check that property needs to be performed before
  * relying on the EffectsAnalysis features.
  * TODO: we might integrate the limited alias analysis for pattern matching with substitution inside here
  *       Or better, we should introduce a simple AliasAnalysis class that provide functionalities.
  */
trait EffectsAnalyzer extends oo.CachingPhase {
  val s: Trees
  val t: s.type
  import s._
  import exprOps._

  private[this] val effectsCache = new ExtractionCache[FunDef, Result]((fd, context) =>
    getDependencyKey(fd.id)(context.symbols)
  )

  protected case class Result(
    effects: Map[FunAbstraction, Set[Effect]],
    locals: Map[Identifier, FunAbstraction]) {

    def merge(that: Result): Result = Result(effects ++ that.effects, locals ++ that.locals)
  }

  protected object Result {
    def empty: Result = Result(Map.empty, Map.empty)
  }

  protected type TransformerContext <: EffectsAnalysis

  trait EffectsAnalysis { self: TransformerContext =>
    implicit val symbols: s.Symbols

    private[this] def functionEffects(fd: FunAbstraction, current: Result): Set[Effect] =
      exprOps.withoutSpecs(fd.fullBody) match {
        case Some(body) =>
          expressionEffects(body, current)
        case None if !fd.flags.exists(_.name == "pure") =>
          fd.params
            .filter(vd => !vd.flags.exists(_.name == "pure") && symbols.isMutableType(vd.getType))
            .map(_.toVariable)
            .map(Effect(_, Path(Seq.empty)))
            .toSet
        case _ =>
          Set.empty
      }

    private[this] val result: Result = symbols.functions.values.foldLeft(Result.empty) {
      case (results, fd) =>
        val fds = (symbols.transitiveCallees(fd) + fd).toSeq.sortBy(_.id)
        val lookups = fds.map(effectsCache get (_, this))
        val newFds = (fds zip lookups).filter(_._2.isEmpty).map(_._1)
        val prevResult = lookups.flatten.foldLeft(Result.empty)(_ merge _)

        val newResult = if (newFds.isEmpty) {
          prevResult
        } else {
          val inners = newFds.map { fd =>
            fd -> collect[FunAbstraction] {
              case LetRec(fds, _) => fds.map(Inner(_)).toSet
              case _ => Set.empty
            } (fd.fullBody)
          }.toMap

          val baseResult = Result(
            inners.flatMap { case (fd, inners) => inners + Outer(fd) }.map(_ -> Set.empty[Effect]).toMap,
            inners.flatMap { case (_, inners) => inners.map(fun => fun.id -> fun) }.toMap)

          val result = inox.utils.fixpoint[Result] { case res @ Result(effects, locals) =>
            Result(effects.map { case (fd, _) => fd -> functionEffects(fd, res) }, locals)
          } (prevResult merge baseResult)

          for ((fd, inners) <- inners) {
            effectsCache(fd, this) = Result(
              result.effects.filter { case (fun, _) => fun == Outer(fd) || inners(fun) },
              result.locals.filter { case (_, fun) => inners(fun) }
            )
          }

          result
        }

        results merge newResult
    }

    def effects(fd: FunDef): Set[Effect] = result.effects(Outer(fd))
    def effects(fun: FunAbstraction): Set[Effect] = result.effects(fun)
    def effects(expr: Expr): Set[Effect] = expressionEffects(expr, result)

    private[imperative] def local(id: Identifier): FunAbstraction = result.locals(id)

    private[imperative] def getAliasedParams(fd: FunAbstraction): Seq[ValDef] = {
      val receivers = effects(fd).map(_.receiver)
      fd.params.filter(vd => receivers(vd.toVariable))
    }

    private[imperative] def getReturnType(fd: FunAbstraction): Type = {
      val aliasedParams = getAliasedParams(fd)
      tupleTypeWrap(fd.returnType +: aliasedParams.map(_.tpe))
    }

    def asString(implicit printerOpts: PrinterOptions): String =
      s"EffectsAnalysis(effects: ${result.effects.map(e => e._1.id -> e._2)}, locals: ${result.locals})"

    override def toString: String = asString
  }

  sealed abstract class Accessor
  case class ADTFieldAccessor(selector: Identifier) extends Accessor
  case class ClassFieldAccessor(selector: Identifier) extends Accessor
  case class ArrayAccessor(index: Expr) extends Accessor

  case class Path(path: Seq[Accessor]) {
    def :+(elem: Accessor): Path = Path(path :+ elem)
    def +:(elem: Accessor): Path = Path(elem +: path)
    def ++(that: Path): Path = Path(this.path ++ that.path)

    def on(that: Expr)(implicit symbols: Symbols): Option[Target] = {
      def rec(expr: Expr, path: Seq[Accessor]): Option[Expr] = path match {
        case ADTFieldAccessor(id) +: xs =>
          rec(ADTSelector(expr, id), xs)

        case ClassFieldAccessor(id) +: xs =>
          symbols.classForField(expr.getType.asInstanceOf[ClassType], id) match {
            case Some(tcd) => rec(ClassSelector(AsInstanceOf(expr, tcd.toType), id), xs)
            case None => None
          }

        case ArrayAccessor(idx) +: xs =>
          rec(ArraySelect(expr, idx), xs)

        case Seq() =>
          Some(expr)
      }

      rec(that, path).flatMap(getEffect)
    }

    def prefixOf(that: Path): Boolean = {
      def rec(p1: Seq[Accessor], p2: Seq[Accessor]): Boolean = (p1, p2) match {
        case (Seq(), _) => true
        case (ArrayAccessor(_) +: xs1, ArrayAccessor(_) +: xs2) =>
          rec(xs1, xs2)
        case (ADTFieldAccessor(id1) +: xs1, ADTFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case (ClassFieldAccessor(id1) +: xs1, ClassFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case _ => false
      }

      rec(path, that.path)
    }

    def toSeq: Seq[Accessor] = path

    def asString(implicit printerOpts: PrinterOptions): String = path.map {
      case ADTFieldAccessor(id) => s".${id.asString}"
      case ClassFieldAccessor(id) => s".${id.asString}"
      case ArrayAccessor(idx) => s"(${idx.asString})"
    }.mkString("")

    override def toString: String = asString
  }

  object Path {
    def empty: Path = Path(Seq.empty)
  }

  sealed abstract class Target {
    val receiver: Variable

    def +(elem: Accessor): Target = this match {
      case SimpleTarget(receiver, path) =>
        SimpleTarget(receiver, path :+ elem)
      case ConditionalTarget(cond, thn, els) =>
        ConditionalTarget(cond, thn + elem, els + elem)
    }

    def append(that: Target): Target = (this, that) match {
      case (SimpleTarget(receiver, a), SimpleTarget(_, b)) =>
        SimpleTarget(receiver, a ++ b)

      case (SimpleTarget(receiver, path), ConditionalTarget(cond, thn, els)) =>
        ConditionalTarget(cond, thn prependPath path, els prependPath path)

      case (ConditionalTarget(cond, thn, els), that) =>
        ConditionalTarget(cond, thn append that, els append that)
    }

    def prependPath(path: Path): Target = this match {
      case SimpleTarget(receiver, p) =>
        SimpleTarget(receiver, path ++ p)

      case ConditionalTarget(cond, thn, els) =>
        ConditionalTarget(cond, thn prependPath path, els prependPath path)
    }

    def toEffect: Set[Effect] = this match {
      case SimpleTarget(receiver, path) => Set(Effect(receiver, path))
      case ConditionalTarget(_, thn, els) => thn.toEffect ++ els.toEffect
    }
  }

  case class SimpleTarget(
    receiver: Variable,
    path: Path
  ) extends Target

  case class ConditionalTarget(
    condition: Expr,
    whenTrue: Target,
    whenFalse: Target
  ) extends Target {
    require(whenTrue.receiver == whenFalse.receiver)
    val receiver = whenTrue.receiver
  }

  case class Effect(receiver: Variable, path: Path) {
    def +(elem: Accessor) = Effect(receiver, path :+ elem)

    def on(that: Expr)(implicit symbols: Symbols): Option[Effect] = for {
      SimpleTarget(receiver, path) <- this.path on that
    } yield Effect(receiver, path)

    def prefixOf(that: Effect): Boolean =
      receiver == that.receiver && (path prefixOf that.path)

    def toTarget: Target = SimpleTarget(receiver, path)

    def asString(implicit printerOpts: PrinterOptions): String =
      s"Effect(${receiver.asString}${path.asString})"

    override def toString: String = asString
  }

  def getEffect(expr: Expr)(implicit symbols: Symbols): Option[Target] = {
    def rec(expr: Expr, path: Seq[Accessor]): Option[Target] = expr match {
      case v: Variable => Some(SimpleTarget(v, Path(path)))
      case _ if variablesOf(expr).forall(v => !symbols.isMutableType(v.tpe)) => None
      case ADTSelector(e, id) => rec(e, ADTFieldAccessor(id) +: path)
      case ClassSelector(e, id) => rec(e, ClassFieldAccessor(id) +: path)
      case ArraySelect(a, idx) => rec(a, ArrayAccessor(idx) +: path)

      case ADT(id, _, args) => path match {
        case ADTFieldAccessor(fid) +: rest =>
          rec(args(symbols.getConstructor(id).fields.indexWhere(_.id == fid)), rest)
        case _ =>
          throw MissformedStainlessCode(expr, s"Couldn't compute effect targets in: $expr")
      }

      case ClassConstructor(ct, args) => path match {
        case ClassFieldAccessor(fid) +: rest =>
          rec(args(ct.tcd.fields.indexWhere(_.id == fid)), rest)
        case _ =>
          throw MissformedStainlessCode(expr, s"Couldn't compute effect targets in: $expr")
      }

      case Assert(_, _, e) => rec(e, path)
      case Annotated(e, _) => rec(e, path)

      case m: MatchExpr =>
        rec(symbols.matchToIfThenElse(m), path)

      case IfExpr(cnd, thn, els) =>
        for {
          // c <- getEffect(cnd)
          t <- rec(thn, path)
          e <- rec(els, path)
          if t.receiver == e.receiver
        } yield ConditionalTarget(cnd, t, e)

      case fi: FunctionInvocation if fi.tfd.flags.exists(_.name == "accessor") =>
        rec(symbols.simplifyLets(fi.inlined), path)

      case fi: FunctionInvocation => None
      case (_: ApplyLetRec | _: Application) => None
      case (_: FiniteArray | _: LargeArray | _: ArrayUpdated) => None
      case IsInstanceOf(e, _) => rec(e, path)
      case AsInstanceOf(e, _) => rec(e, path)
      case Old(_) => None

      case Let(vd, e, b) if !symbols.isMutableType(vd.tpe) =>
        rec(b, path)

      case Let(vd, e, b) => (getEffect(e), rec(b, path)) match {
        case (Some(ee), Some(be)) if be.receiver == vd.toVariable =>
          Some(ee append be)
        case (_, Some(be)) => Some(be)
        case _ =>
          throw MissformedStainlessCode(expr, s"Couldn't compute effect targets in: $expr")
      }

      case _ =>
        throw MissformedStainlessCode(expr, s"Couldn't compute effect targets in: $expr")
    }

    rec(expr, Seq.empty)
  }

  def getExactEffect(expr: Expr)(implicit symbols: Symbols): Target = getEffect(expr) match {
    case Some(effect) => effect
    case _ => throw MissformedStainlessCode(expr, s"Couldn't compute exact effect targets in: $expr")
  }

  def getKnownEffect(expr: Expr)(implicit symbols: Symbols): Option[Target] = try {
    getEffect(expr)
  } catch {
    case _: MissformedStainlessCode => None
  }

  /** Return all effects of expr
    *
    * Effects of expr are any free variables in scope (either local vars
    * already defined in the scope containing expr, or global var) that
    * are re-assigned by an operation in the expression. An effect is
    * also a mutation of an object refer by an id defined in the scope.
    *
    * This is a conservative analysis, not taking into account control-flow.
    * The set of effects is not definitely effects, but any identifier
    * not in the set will for sure have no effect.
    *
    * We are assuming no aliasing.
    */
  private def expressionEffects(expr: Expr, result: Result)(implicit symbols: Symbols): Set[Effect] = {
    import symbols._
    val freeVars = variablesOf(expr)

    def inEnv(effect: Effect, env: Map[Variable, Effect]): Option[Effect] =
      env.get(effect.receiver).map(e => e.copy(path = e.path ++ effect.path))

    def effect(expr: Expr, env: Map[Variable, Effect]): Set[Effect] =
      getEffect(expr).toSet flatMap { (target: Target) =>
        target.toEffect.flatMap(eff => inEnv(eff, env).toSet)
      }

    def rec(expr: Expr, env: Map[Variable, Effect]): Set[Effect] = expr match {
      case Let(vd, e, b) if symbols.isMutableType(vd.tpe) =>
        rec(e, env) ++ rec(b, env ++ effect(e, env).map(vd.toVariable -> _))

      case MatchExpr(scrut, cses) if symbols.isMutableType(scrut.getType) =>
        rec(scrut, env) ++ cses.flatMap { case MatchCase(pattern, guard, rhs) =>
          val newEnv = env ++ mapForPattern(scrut, pattern).flatMap {
            case (v, e) => effect(e, env).map(v.toVariable -> _)
          }
          guard.toSeq.flatMap(rec(_, newEnv)).toSet ++ rec(rhs, newEnv)
        }

      case ArrayUpdate(o, idx, v) =>
        rec(o, env) ++ rec(idx, env) ++ rec(v, env) ++
        effect(o, env).map(_ + ArrayAccessor(idx))

      case FieldAssignment(o, id, v) =>
        val accessor = o.getType match {
          case _: ADTType => ADTFieldAccessor(id)
          case _: ClassType => ClassFieldAccessor(id)
        }

        rec(o, env) ++ rec(v, env) ++ effect(o, env).map(_ + accessor)

      case Application(callee, args) =>
        val ft @ FunctionType(_, _) = callee.getType
        val effects = functionTypeEffects(ft)
        rec(callee, env) ++ args.flatMap(rec(_, env)) ++
        args.map(effect(_, env)).zipWithIndex
          .filter(p => effects contains p._2)
          .flatMap(_._1)

      case Assignment(v, value) => rec(value, env) ++ env.get(v)

      case IfExpr(cnd, thn, els) =>
        rec(cnd, env) ++ rec(thn, env) ++ rec(els, env)

      case fi @ FunInvocation(id, tps, args, _) =>
        val fun = fi match {
          case FunctionInvocation(id, _, _) => Outer(getFunction(id))
          case ApplyLetRec(id, _, _, _, _) => result.locals(id)
        }

        val currentEffects: Set[Effect] = result.effects(fun)
        val paramSubst = (fun.params.map(_.toVariable) zip args).toMap
        val invocEffects = currentEffects.flatMap(e => paramSubst.get(e.receiver) match {
          case Some(arg) => (e on arg).flatMap(inEnv(_, env))
          case None => Seq(e) // This effect occurs on some variable captured from scope
        })

        val effectsOnFreeVars = invocEffects.filter(e => freeVars contains e.receiver)
        val effectsOnLocalFreeVars = currentEffects.filterNot(e => paramSubst contains e.receiver)
        effectsOnFreeVars ++ effectsOnLocalFreeVars ++ args.flatMap(rec(_, env))

      case Operator(es, _) => es.flatMap(rec(_, env)).toSet
    }

    val mutated = rec(expr, freeVars.map(v => v -> Effect(v, Path.empty)).toMap)

    // We truncate the effects path if it goes through an inductive ADT as
    // such effects can lead to inexistence of the effects fixpoint.
    // We also truncate array paths as they rely on some index that is not
    // necessarily well-scoped (and could itself have effects).
    def truncate(effect: Effect): Effect = {
      def isInductive(tpe: Type, seen: Set[Identifier]): Boolean = {
        val deps = s.typeOps.collect {
          case ADTType(id, _) => dependencies(id)
          case ClassType(id, _) => dependencies(id)
          case _ => Set.empty[Identifier]
        } (tpe)

        (seen & deps).nonEmpty
      }

      def rec(tpe: Type, path: Seq[Accessor], seen: Set[Identifier]): Seq[Accessor] = (tpe, path) match {
        case (adt: ADTType, (fa @ ADTFieldAccessor(id)) +: xs) =>
          val field = adt.getSort.constructors.flatMap(_.fields).find(_.id == id).get
          if (isInductive(field.getType, seen)) Seq()
          else fa +: rec(field.getType, xs, seen + adt.id)
        case (ct: ClassType, (fa @ ClassFieldAccessor(id)) +: xs) =>
          val field = getClassField(ct, id).get
          if (isInductive(field.getType, seen)) Seq()
          else fa +: rec(field.getType, xs, seen + ct.id)
        case (_, ArrayAccessor(_) +: xs) => Seq()
        case _ => Seq()
      }

      Effect(effect.receiver, Path(rec(effect.receiver.getType, effect.path.toSeq, Set())))
    }

    // We merge paths that are prefixes of one another or point to the same array
    def merge(paths: Set[Path]): Set[Path] = {
      // This truncates the path `p2` depending on `p1`
      def rec(p1: Seq[Accessor], p2: Seq[Accessor]): Option[Path] = (p1, p2) match {
        case (ArrayAccessor(idx1) +: xs1, ArrayAccessor(idx2) +: xs2) if idx1 != idx2 => Some(Path.empty)
        case (x1 +: xs1, x2 +: xs2) if x1 == x2 => rec(xs1, xs2).map(x1 +: _)
        case (Nil, Nil) => Some(Path.empty)
        case _ => None
      }

      val merged = paths.flatMap { t1 =>
        paths.flatMap { t2 =>
          rec(t1.toSeq, t2.toSeq)
        } + t1
      }

      merged.filterNot(t1 => (merged - t1).exists(t2 => t2 prefixOf t1))
    }

    mutated
      .map(truncate)
      .groupBy(_.receiver)
      .flatMap { case (v, effects) => merge(effects.map(_.path)).map(Effect(v, _)) }.toSet
  }

  /** Effects at the level of types for a function
    *
    * This disregards the actual implementation of a function, and considers only
    * its type to determine a conservative abstraction of its effects.
    *
    * In theory this can be overriden to use a different behaviour.
    */
  def functionTypeEffects(ft: FunctionType)(implicit symbols: Symbols): Set[Int] = {
    ft.from.zipWithIndex.flatMap { case (tpe, i) =>
      if (symbols.isMutableType(tpe)) Some(i) else None
    }.toSet
  }
}
