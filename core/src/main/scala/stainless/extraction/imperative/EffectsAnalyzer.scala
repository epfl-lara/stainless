/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.FatalError

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

    def asString(implicit printerOpts: PrinterOptions): String = {
      val effectsString = effects.map(e => "  " + e._1.id.asString + " -> " + e._2.map(_.asString)).toList.sorted.mkString("\n")
      val localsString = locals.map(p => "  " + p._1.asString + "," + p._2.asString).toList.sorted.mkString("\n")
      s"""|effects:
          |$effectsString
          |
          |locals:
          |$localsString""".stripMargin
    }
  }

  protected object Result {
    def empty: Result = Result(Map.empty, Map.empty)
  }

  protected type TransformerContext <: EffectsAnalysis

  trait EffectsAnalysis { self: TransformerContext =>
    implicit val symbols: s.Symbols

    private[this] def functionEffects(fd: FunAbstraction, current: Result): Set[Effect] =
      BodyWithSpecs(fd.fullBody).bodyOpt match {
        case Some(body) =>
          expressionEffects(body, current)
        case None if !fd.flags.contains(IsPure) =>
          fd.params
            .filter(vd => symbols.isMutableType(vd.getType) && !vd.flags.contains(IsPure))
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
            inners.flatMap { case (_, inners) => inners.map(fun => fun.id -> fun) })

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
      s"EffectsAnalysis(\n${result.asString}\n)"

    override def toString: String = asString
  }

  sealed abstract class Accessor {
    def asString(implicit ctx: inox.Context): String
  }

  case class ADTFieldAccessor(selector: Identifier) extends Accessor {
    def asString(implicit ctx: inox.Context) = s"ADTFieldAccessor(${selector.asString})"
  }

  case class ClassFieldAccessor(selector: Identifier) extends Accessor {
    def asString(implicit ctx: inox.Context) = s"ClassFieldAccessor(${selector.asString})"
  }

  case class ArrayAccessor(index: Expr) extends Accessor {
    def asString(implicit ctx: inox.Context) = s"ArrayAccessor(${index.asString})"
  }

  case class MutableMapAccessor(index: Expr) extends Accessor {
    def asString(implicit ctx: inox.Context) = s"MutableMapAccessor(${index.asString})"
  }

  case class TupleFieldAccessor(index: Int) extends Accessor {
    def asString(implicit ctx: inox.Context) = s"TupleFieldAccessor($index)"
  }

  case class Path(path: Seq[Accessor]) {
    def :+(elem: Accessor): Path = Path(path :+ elem)
    def +:(elem: Accessor): Path = Path(elem +: path)
    def ++(that: Path): Path = Path(this.path ++ that.path)

    def wrap(expr: Expr)(implicit symbols: Symbols) = Path.wrap(expr, path)

    def on(that: Expr)(implicit symbols: Symbols): Set[Target] = {
      wrap(that).toSet.flatMap(getTargets)
    }

    def prefixOf(that: Path): Boolean = {
      // TODO: more expressions can be added to be "provably different"
      def provablyDifferent(index1: Expr, index2: Expr): Boolean = (index1, index2) match {
        case (x1: Variable, Plus(x2: Variable, BVLiteral(_, _, size)))
          if x1 == x2 && x1.tpe == BVType(true, 32) && size <= 32 => true
        case (Plus(x2: Variable, BVLiteral(_, _, size)), x1: Variable)
          if x1 == x2 && x1.tpe == BVType(true, 32) && size <= 32 => true
        case (BVLiteral(signed1, value1, size1), BVLiteral(signed2, value2, size2))
          if value1 != value2 => true
        case _ => false
      }

      def rec(p1: Seq[Accessor], p2: Seq[Accessor]): Boolean = (p1, p2) match {
        case (Seq(), _) => true
        case (ArrayAccessor(index1) +: xs1, ArrayAccessor(index2) +: xs2) if !provablyDifferent(index1, index2) =>
          rec(xs1, xs2)
        case (ADTFieldAccessor(id1) +: xs1, ADTFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case (ClassFieldAccessor(id1) +: xs1, ClassFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case (TupleFieldAccessor(id1) +: xs1, TupleFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case (MutableMapAccessor(_) +: xs1, MutableMapAccessor(_) +: xs2) =>
          rec(xs1, xs2)
        case _ => false
      }

      rec(path, that.path)
    }

    def toSeq: Seq[Accessor] = path

    def asString(implicit printerOpts: PrinterOptions): String =
      if (path.isEmpty) "<empty>"
      else path.map {
        case ADTFieldAccessor(id) => s".${id.asString}"
        case ClassFieldAccessor(id) => s".${id.asString}"
        case TupleFieldAccessor(idx) => s"._$idx"
        case ArrayAccessor(idx) => s"(${idx.asString})"
        case MutableMapAccessor(idx) => s"(${idx.asString})"
      }.mkString("")

    override def toString: String = asString
  }

  object Path {
    def empty: Path = Path(Seq.empty)

    def wrap(expr: Expr, path: Seq[Accessor])(implicit symbols: Symbols): Option[Expr] = path match {
      case ADTFieldAccessor(id) +: xs =>
        wrap(ADTSelector(expr, id), xs)

      case TupleFieldAccessor(idx) +: xs =>
        wrap(TupleSelect(expr, idx), xs)

      case ClassFieldAccessor(id) +: xs =>
        def asClassType(tpe: Type): Option[ClassType] = tpe match {
          case ct: ClassType => Some(ct)
          case ta: TypeApply if !ta.isAbstract => asClassType(ta.resolve)
          case other => None
        }

        for {
          ct  <- asClassType(expr.getType)
          tcd <- symbols.classForField(ct, id)
          res <- wrap(ClassSelector(AsInstanceOf(expr, tcd.toType), id), xs)
        } yield res

      case ArrayAccessor(idx) +: xs =>
        wrap(ArraySelect(expr, idx), xs)

      case MutableMapAccessor(idx) +: xs =>
        wrap(MutableMapApply(expr, idx), xs)

      case Seq() =>
        Some(expr)
    }

  }

  case class Target(receiver: Variable, condition: Option[Expr], path: Path) {
    def +(elem: Accessor): Target = Target(receiver, condition, path :+ elem)

    def append(that: Target): Target = (condition, that.condition) match {
      case (condition, None) =>
        Target(receiver, condition, path ++ that.path)
      case (None, _) =>
        Target(receiver, that.condition, path ++ that.path)
      case (Some(condition), Some(thatCondition)) =>
        Target(receiver, Some(And(condition, thatCondition)), path ++ that.path)
    }

    def prependPath(path: Path): Target = Target(receiver, condition, path ++ this.path)

    def toEffect: Effect = Effect(receiver, path)

    def asString(implicit printerOpts: PrinterOptions): String =
      s"Target(${receiver.asString}, ${condition.map(_.asString)}, ${path.asString})"

    override def toString: String = asString

    def isValid(implicit syms: Symbols): Boolean = {
      def rec(tpe: Type, path: Seq[Accessor]): Boolean = (tpe, path) match {
        case (adt: ADTType, ADTFieldAccessor(id) +: xs) =>
          val constructors = adt.getSort.constructors
          val constructor = constructors.find(_.fields.exists(_.id == id))
          val field = constructor.flatMap(_.fields.find(_.id == id))
          field.isDefined && rec(field.get.getType, xs)

        case (ct: ClassType, ClassFieldAccessor(id) +: xs) =>
          val field = syms.classForField(ct, id).flatMap(_.fields.find(_.id == id))
          field.isDefined && rec(field.get.getType, xs)

        case (tt: TupleType, TupleFieldAccessor(idx) +: xs) =>
          0 < idx && idx <= tt.dimension && rec(tt.bases(idx - 1), xs)

        case (ArrayType(base), ArrayAccessor(idx) +: xs) =>
          rec(base, xs)

        case (_, Nil) =>
          true
      }

      rec(receiver.getType, path.toSeq)
    }
  }

  case class Effect(receiver: Variable, path: Path) {
    def +(elem: Accessor) = Effect(receiver, path :+ elem)

    def on(that: Expr)(implicit symbols: Symbols): Set[Effect] = for {
      Target(receiver, _, path) <- this.path on that
    } yield Effect(receiver, path)

    def prefixOf(that: Effect): Boolean =
      receiver == that.receiver && (path prefixOf that.path)

    def toTarget: Target = Target(receiver, None, path)

    def wrap(implicit symbols: Symbols): Option[Expr] = path.wrap(receiver)

    def targetString(implicit printerOpts: PrinterOptions): String =
      s"${receiver.asString}${path.asString}"

    def asString(implicit printerOpts: PrinterOptions): String =
      s"Effect($targetString)"

    override def toString: String = asString
  }

  // getTargets(expr, Seq()) returns the set of targets such that after `var x = expr`,
  // the modifications on `x` will result in modifications on these targets
  def getTargets(expr: Expr, path: Seq[Accessor])(implicit symbols: Symbols): Set[Target] = expr match {
    case _ if variablesOf(expr).forall(v => !symbols.isMutableType(v.tpe)) => Set.empty
    case v: Variable => Set(Target(v, None, Path(path)))
    case ADTSelector(e, id) => getTargets(e, ADTFieldAccessor(id) +: path)
    case ClassSelector(e, id) => getTargets(e, ClassFieldAccessor(id) +: path)
    case TupleSelect(e, idx) => getTargets(e, TupleFieldAccessor(idx) +: path)
    case ArraySelect(a, idx) => getTargets(a, ArrayAccessor(idx) +: path)
    case MutableMapApply(a, idx) => getTargets(a, MutableMapAccessor(idx) +: path)
    case MutableMapDuplicate(m) => getTargets(m, path)

    case ADT(id, _, args) => path match {
      case ADTFieldAccessor(fid) +: rest =>
        getTargets(args(symbols.getConstructor(id).fields.indexWhere(_.id == fid)), rest)
      case _ =>
        Set.empty
    }

    case ClassConstructor(ct, args) => path match {
      case ClassFieldAccessor(fid) +: rest =>
        getTargets(args(ct.tcd.fields.indexWhere(_.id == fid)), rest)
      case _ =>
        Set.empty
    }

    case Tuple(exprs) => path match {
      case TupleFieldAccessor(idx) +: rest =>
        getTargets(exprs(idx - 1), rest)
      case _ =>
        Set.empty
    }

    case FiniteArray(elems, _) => path match {
      case ArrayAccessor(bv: BVLiteral) +: rest =>
        val i = bv.toBigInt.toInt
        if (i < elems.size) getTargets(elems(i), rest)
        else throw MalformedStainlessCode(expr, s"Out of bound array access in ${expr.asString}")
      case _ if path.isEmpty || !path.head.isInstanceOf[ArrayAccessor] =>
        Set.empty
      case _ =>
        throw MalformedStainlessCode(expr, s"Couldn't compute effect targets in finite array ${expr.asString}")
    }

    case Assert(_, _, e) => getTargets(e, path)
    case Annotated(e, _) => getTargets(e, path)

    case m: MatchExpr =>
      getTargets(symbols.matchToIfThenElse(m), path)

    case IfExpr(cnd, thn, els) =>
      def notConj(cnd: Expr, e: Option[Expr])(): Expr = e map { e =>
        And(Not(cnd).setPos(cnd), e.setPos(cnd)).setPos(cnd)
      } getOrElse(Not(cnd).setPos(cnd))

      def conj(cnd: Expr, e: Option[Expr])(): Expr = e map { e =>
        And(cnd, e.setPos(cnd)).setPos(cnd)
      } getOrElse(cnd)

      for {
        t <- getTargets(thn, path)
        e <- getTargets(els, path)
        target <- Set(
          Target(t.receiver, Some(conj(cnd, t.condition)), t.path),
          Target(e.receiver, Some(notConj(cnd, e.condition)), e.path)
        ) if target.isValid
      } yield target

    case fi: FunctionInvocation if !symbols.isRecursive(fi.id) =>
      if (fi.tfd.flags.contains(IsPure)) Set.empty
      else BodyWithSpecs(symbols.simplifyLets(fi.inlined))
        .bodyOpt
        .map(getTargets(_, path))
        .getOrElse(Set.empty)

    case fi: FunctionInvocation => Set.empty
    case (_: ApplyLetRec | _: Application) => Set.empty
    case _: LargeArray | _: ArrayUpdated if path.isEmpty || !path.head.isInstanceOf[ArrayAccessor] => Set.empty
    case _: MutableMapUpdated => Set.empty
    case IsInstanceOf(e, _) => getTargets(e, path)
    case AsInstanceOf(e, _) => getTargets(e, path)
    case Old(_) => Set.empty
    case Snapshot(_) => Set.empty
    case FreshCopy(_) => Set.empty

    case ArrayLength(_) => Set.empty

    case FiniteSet(elements, tpe) => Set.empty
    case SetUnion(s1, s2) => Set.empty
    case SetIntersection(s1, s2) => Set.empty
    case SetDifference(s1, s2) => Set.empty
    case SubsetOf(s1, s2) => Set.empty
    case ElementOfSet(element, set) => Set.empty
    case SetAdd(bag, element) => Set.empty

    case FiniteBag(elements, tpe) => Set.empty
    case BagUnion(s1, s2) => Set.empty
    case BagIntersection(s1, s2) => Set.empty
    case BagDifference(s1, s2) => Set.empty
    case MultiplicityInBag(element, bag) => Set.empty
    case BagAdd(bag, element) => Set.empty

    case Block(_, last) => getTargets(last, path)

    case Let(vd, e, b) if !symbols.isMutableType(vd.tpe) =>
      getTargets(b, path)

    case Let(vd, e, b) =>
      val bEffects = getTargets(b, path)
      for (ee <- getTargets(e); be <- bEffects) yield {
        if (be.receiver == vd.toVariable) ee.append(be) else be
      }

    case _ if !symbols.isMutableType(expr.getType) => Set.empty

    case _ =>
      throw MalformedStainlessCode(expr,
        s"Couldn't compute effect targets in (${expr.getClass}): ${expr.asString}\n" +
        s"Path: ${path.map(_.asString)}"
      )
  }

  def getTargets(expr: Expr)(implicit symbols: Symbols): Set[Target] = {
    getTargets(expr, Seq.empty)
  }

  protected def typeToAccessor(tpe: Type, id: Identifier)(implicit s: Symbols): Accessor = tpe match {
    case at: ADTType   => ADTFieldAccessor(id)
    case ct: ClassType => ClassFieldAccessor(id)
    case ta: TypeApply => typeToAccessor(ta.getType, id)
    case _ => throw FatalError(s"Cannot have accessors over type $tpe")
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
      getTargets(expr) flatMap { (target: Target) =>
        inEnv(target.toEffect, env).toSet
      }

    def rec(expr: Expr, env: Map[Variable, Effect]): Set[Effect] = expr match {
      case Let(vd, e, b) if symbols.isMutableType(vd.tpe) =>
        if ((variablesOf(e) & variablesOf(b)).forall(v => !isMutableType(v.tpe))) {
          val effe = rec(e, env)
          val newEnv = (variablesOf(b) ++ freeVars).map(v => v -> Effect(v, Path.empty)).toMap
          val effb = rec(b, newEnv)
          effe ++ effb.flatMap { case ef @ Effect(receiver, path) =>
            if (receiver == vd.toVariable) getTargets(e, path.toSeq).map(_.toEffect)
            else Set(ef)
          }.flatMap(inEnv(_, env))
        }
        else
          rec(e, env) ++ rec(b, env ++ effect(e, env).map(vd.toVariable -> _))

      case MatchExpr(scrut, cses) if symbols.isMutableType(scrut.getType) =>
        rec(scrut, env) ++ cses.flatMap { case MatchCase(pattern, guard, rhs) =>
          val newEnv = env ++ mapForPattern(scrut, pattern).flatMap {
            case (v, e) => effect(e, env).map(v.toVariable -> _)
          }
          guard.toSeq.flatMap(rec(_, newEnv)).toSet ++ rec(rhs, newEnv)
        }

      case Swap(array1, index1, array2, index2) =>
        rec(array1, env) ++ rec(index1, env) ++ rec(array2, env) ++ rec(index2, env) ++
        effect(array1, env).map(_ + ArrayAccessor(index1)) ++
        effect(array2, env).map(_ + ArrayAccessor(index2))

      case ArrayUpdate(o, idx, v) =>
        rec(o, env) ++ rec(idx, env) ++ rec(v, env) ++
        effect(o, env).map(_ + ArrayAccessor(idx))

      case MutableMapUpdate(map, key, value) =>
        rec(map, env) ++ rec(key, env) ++ rec(value, env) ++
        effect(map, env).map(_ + MutableMapAccessor(key))

      case MutableMapUpdated(map, key, value) =>
        rec(map, env) ++ rec(key, env) ++ rec(value, env)

      case MutableMapDuplicate(map) =>
        rec(map, env)

      case fa @ FieldAssignment(o, id, v) =>
        val accessor = typeToAccessor(o.getType, id)
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
    * In theory this can be overridden to use a different behaviour.
    */
  def functionTypeEffects(ft: FunctionType)(implicit symbols: Symbols): Set[Int] = {
    ft.from.zipWithIndex.flatMap { case (tpe, i) =>
      if (symbols.isMutableType(tpe)) Some(i) else None
    }.toSet
  }
}
