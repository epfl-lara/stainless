/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

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
trait EffectsAnalysis {
  val trees: Trees
  val symbols: trees.Symbols
  import trees._
  import symbols._

  private lazy val outers = symbols.functions.values.map(Outer(_)).toSeq
  private lazy val inners = outers.flatMap(fd => exprOps.collect[Inner] {
    case LetRec(fds, _) => fds.map(Inner(_)).toSet
    case _ => Set.empty
  } (fd.body))

  private lazy val locals: Map[Variable, FunAbstraction] = inners.map(inner => inner.fd.name.toVariable -> inner).toMap

  // fill up the global map!
  private lazy val effects: Map[FunAbstraction, Set[Variable]] = {
    inox.utils.fixpoint { (effects: Map[FunAbstraction, Set[Variable]]) =>
      effects.keys.map(fd => fd -> {
        exprOps.withoutSpec(fd.body).map(body => expressionEffects(body, effects)).getOrElse(Set.empty)
      }).toMap
    } ((outers ++ inners).map(fd => fd -> Set.empty[Variable]).toMap)
  }

  //TODO: should return a set of ids (to support local fundef)
  def apply(fd: FunDef): Set[Int] = apply(Outer(fd))
  def apply(fd: FunAbstraction): Set[Int] = effectsIndices(fd, effects(fd))

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
  def apply(expr: Expr): Set[Variable] = expressionEffects(expr, effects)

  private def expressionEffects(expr: Expr, effects: Map[FunAbstraction, Set[Variable]]): Set[Variable] = {
    val freeVars = exprOps.variablesOf(expr)
    //println("computing effects of: " + expr)

    val firstLevelMutated: Set[Variable] = {
      val localAliases = freeVars.map(v => v -> computeLocalAliases(v, expr)).toMap
      freeVars.filter { v =>
        val aliases = localAliases(v)
        exprOps.exists(expr => aliases.exists(v => isMutationOf(expr, v)))(expr)
      }
    }

    val secondLevelMutated: Set[Variable] = {
      val calls = exprOps.collect[(FunAbstraction, Seq[Expr])] {
        case fi @ FunctionInvocation(_, _, args) => Set(Outer(fi.tfd.fd) -> args)
        case ApplyLetRec(v, _, args) => Set(locals(v) -> args)
        case _ => Set.empty
      } (expr)

      calls.flatMap { case (fd, args) =>
        val fdCurrentEffects: Set[Variable] = effects(fd)
        val invocEffects = fdCurrentEffects.flatMap(v => findArgumentForParam(fd, args, v) match {
          case Some(arg) => getReferencedVariables(arg)
          case None => Set(v) //this v is captured from scope and not an actual function parameter
        })

        val effectsOnLocalFreeVars = fdCurrentEffects -- fd.params.map(_.toVariable)
        (freeVars intersect invocEffects) ++ effectsOnLocalFreeVars
      }
    }

    firstLevelMutated ++ secondLevelMutated
  }


  private val mutableTypes: MutableMap[Type, Boolean] = MutableMap.empty

  /** Determine if the type is mutable
    *
    * In Stainless, we classify types as either mutable or immutable. Immutable
    * type can be referenced freely, while mutable types must be treated with
    * care. This function uses a cache, so make sure to not update your class
    * def and use the same instance of EffectsAnalysis. It is fine to add
    * new ClassDef types on the fly, granted that they use fresh identifiers.
    */
  def isMutableType(tpe: Type): Boolean = {
    def rec(tpe: Type, seen: Set[ADTType]): Boolean = mutableTypes.getOrElseUpdate(tpe, tpe match {
      case (tp: TypeParameter) => tp.flags contains IsMutable
      case (arr: ArrayType) => true
      case (adt: ADTType) if seen contains adt => false
      case (adt: ADTType) => adt.getADT match {
        case tsort: TypedADTSort => tsort.constructors.exists(tcons => rec(tcons.toType, seen + adt))
        case tcons: TypedADTConstructor => tcons.fields.exists(vd => (vd.flags contains IsVar) || rec(vd.tpe, seen + adt))
      }
      case _: FunctionType => false
      case NAryType(tps, _) => tps.exists(rec(_, seen))
    })
    rec(tpe, Set())
  }

  /** Effects at the level of types for a function
    *
    * This disregards the actual implementation of a function, and considers only
    * its type to determine a conservative abstraction of its effects.
    *
    * In theory this can be overriden to use a different behaviour.
    */
  def functionTypeEffects(ft: FunctionType): Set[Int] = {
    ft.from.zipWithIndex.flatMap { case (tpe, i) =>
      if (isMutableType(tpe)) Some(i) else None
    }.toSet
  }

  private[imperative] def getAliasedParams(fd: FunAbstraction): Seq[ValDef] = {
    val ownEffects = apply(fd)
    fd.params.zipWithIndex.flatMap {
      case (vd, i) if ownEffects(i) => Some(vd)
      case _ => None
    }
  }

  private[imperative] def getReturnType(fd: FunAbstraction): Type = {
    val aliasedParams = getAliasedParams(fd)
    tupleTypeWrap(fd.returnType +: aliasedParams.map(_.tpe))
  }

  private[imperative] def getReturnedExpressions(expr: Expr): Seq[Expr] = expr match {
    case Let(_, _, rest) => getReturnedExpressions(rest)
    case LetVar(_, _, rest) => getReturnedExpressions(rest)
    case Block(_, rest) => getReturnedExpressions(rest)
    case IfExpr(_, thenn, elze) => getReturnedExpressions(thenn) ++ getReturnedExpressions(elze)
    case MatchExpr(_, cses) => cses.flatMap(cse => getReturnedExpressions(cse.rhs))
    case e => Seq(e)
  }

  private[imperative] def getReferencedVariables(expr: Expr): List[Variable] = expr match {
    case v: Variable => List(v)
    case ADTSelector(e, _) => getReferencedVariables(e)
    case ADT(_, es) => es.flatMap(getReferencedVariables).toList
    case AsInstanceOf(e, _) => getReferencedVariables(e)
    case ArraySelect(a, _) => getReferencedVariables(a)
    case _ => Nil
  }

  private[imperative] def getReceiverVariable(expr: Expr): Option[Variable] = expr match {
    case v: Variable => Some(v)
    case ADTSelector(e, _) => getReceiverVariable(e)
    case AsInstanceOf(e, _) => getReceiverVariable(e)
    case ArraySelect(a, _) => getReceiverVariable(a)
    case _ => None
  }

  /*
   * Check if expr is mutating variable id. This only checks if the expression
   * is the mutation operation, and will not perform expression traversal to
   * see if a sub-expression mutates something.
   */
  private def isMutationOf(expr: Expr, v: Variable): Boolean = expr match {
    case ArrayUpdate(o, _, _) => getReferencedVariables(o).exists(_ == v)
    case FieldAssignment(obj, _, _) => getReferencedVariables(obj).exists(_ == v)
    case Application(callee, args) =>
      val ft @ FunctionType(_, _) = callee.getType
      val effects = functionTypeEffects(ft)
      args.map(getReferencedVariables(_)).zipWithIndex.exists {
        case (argVars, index) => argVars.exists(_ == v) && effects.contains(index)
      }
    case Assignment(v2, _) => v == v2
    case _ => false
  }

  private def showFunDefWithEffect(fdsEffects: Map[FunDef, Set[Identifier]]): String =
    fdsEffects.filter(p => p._2.nonEmpty).map(p => (p._1.id, p._2)).toString

  private def findArgumentForParam(fd: FunAbstraction, args: Seq[Expr], param: Variable): Option[Expr] = {
    val index = fd.params.indexWhere(vd => vd.toVariable == param)
    if (index >= 0) Some(args(index)) else None
  }

  //return the set of modified variables arguments to a function invocation,
  //given the effect of the fun def invoked.
  //private def functionInvocationEffects(fi: FunctionInvocation, effects: Set[Int]): Set[Identifier] = {
  //  fi.args.zipWithIndex.filter(p => effects.contains(p._2)).flatMap{ case (arg, _) => {
  //    findReferencedIds(arg)
  //  }}.toSet

  //  //.map(arg => findReferencedIds(arg)).zipWithIndex.
  //  //
  //  //flatMap{ case (ids, i) =>
  //  //  if(effects.contains(i)) 
  //  //  case (ids, i) if effects.contains(i) => ids
  //  //  case _ => Set[Identifier]()
  //  //}
  //}


  //for a given id, compute the identifiers that alias it or some part of the object refered by id
  private def computeLocalAliases(v: Variable, body: Expr): Set[Variable] = {
    def pre(expr: Expr, vs: Set[Variable]): Set[Variable] = expr match {
      case l @ Let(vd, v: Variable, _) if vs contains v => vs + vd.toVariable
      case m @ MatchExpr(v: Variable, cses) if vs contains v =>
        val newVs = cses.flatMap(mc => mc.pattern.binders).map(_.toVariable)
        vs ++ newVs
      case e => vs
    }
    def combiner(e: Expr, ctx: Set[Variable], vs: Seq[Set[Variable]]): Set[Variable] = ctx ++ vs.toSet.flatten + v
    val res = exprOps.preFoldWithContext(pre, combiner)(body, Set(v))
    res
  }


  //I think this is not needed anymore, and we actually need the findReferencedIds
  //private def findReceiverId(o: Expr): Option[Identifier] = o match {
  //  case Variable(id) => Some(id)
  //  case CaseClassSelector(_, e, _) => findReceiverId(e)
  //  case AsInstanceOf(e, ct) => findReceiverId(e)
  //  case ArraySelect(a, _) => findReceiverId(a)
  //  case _ => None
  //}

  //TODO: as we are clarifying the notion of effects on functions/expression, we probably
  //should use a structure such as a pair of Set[Int] and Set[Identifier] to represent
  //effects

  //returns the set of indices (from its parameters) that the fun def modified, given
  //the set of identifiers that the fun def modifies. It might lose some information
  //such as closure mutating a local variable
  private def effectsIndices(fd: FunAbstraction, vs: Set[Variable]): Set[Int] = {
    vs.map(v => fd.params.indexWhere(_.toVariable == v)).filter(_ != -1)
  }
}
