/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

/** Simple alias analysis functions
  *
  * This provides tree level (no solver involved) alias analysis for Stainless programs.
  * The analysis is flow-insensitive, and thus very conservative.
  * We currently only support a very coarse abstraction of aliasing defined as
  * sharing a part of the heap. For example, if a reference points to some object, and
  * another reference points to a sub-part (like tail in a mutable list kind of object)
  * then the two are considered aliases of each other.
  *
  * This is a conservative analysis, that does not take into account control-flow, and
  * thus, some aliases might actually never share an object at runtime.
  *
  * Each identifier has a set of aliases in a given expression or definition. But, this
  * is not necessarly a partitionning of the set of identifiers. The root pointer of an
  * object would be aliased by two pointers to distinct children of the object, but both
  * children pointers would not be alias of each other.
  *
  * We define aliases even for immutable types. Finding aliases does not depend on mutability
  * or not, so it is straightforward to defined the operations in the general case. This
  * lets AliasAnalysis not being dependent on the EffectAnalysis as well.
  *
  * There is the question of copy assignment versus reference assignment for types such as
  * numbers.
  * {{{ 
  *   val a = 13
  *   val b = a
  * }}}
  * In the above, `b` would actually not be a reference and store an distinct copy of 13. For
  * our analysis purpose, this does not matter too much as we can defer the semantics of assignments
  * to a separate process, and just consider `a` and `b` as aliases to each other.
  *
  * Current implementation is not very precise. If a function takes an object as a paramater and
  * returns a field of the object, it will consider that it aliases the original object (the variable
  * that pointed to the root). We could try to refine it in the future by introduction the notion
  * of path in memory: variable + sequence of fields.
  *
  * The analysis here is independent of the transformation phases in Stainless. Throughout the Stainless pipeline,
  * we make the assumption that very little aliasing is actually done. Typically, functions should
  * never return a reference to a parameter, in order to avoid the creation of multiple reference in a
  * local scope. This AliasAnalysis can be used to check such properties. It does not make any assumption,
  * it computes conservatively aliases created by function invocation and in expressions.
  */
trait AliasAnalysis {
  val trees: Trees
  val symbols: trees.Symbols

  //incremental cache, once a value is set, it is final
  private val fdsAliases: MutableMap[FunDef, Set[Identifier]] = MutableMap.empty

  def aliases(id: Identifier, expr: Expr): Set[Identifier] = {
    ???
  }

  /** Identifiers aliased by the returned value
    *
    * This analyzes the body of the function and determines the set of
    * identifiers that the value taken by the function can alias to.
    * The set of ids is a subset of the function parameters + any global
    * (or in enclosing scope, for nested defs) vals.
    *
    * We assume method lifting has already been performed, so any field access
    * is done via the root object, and the root object is part of the parameters.
    * TODO: maybe we can handle method invoc as well?
    *
    * This needs to transitively checks function invocations as well, and
    * perform some fixpoint computation due to mutually recursive functions.
    */
  def functionAliasing(fd: FunDef): Set[Identifier] = fdsAliases.getOrElseUpdate(fd, {
    computeFunctionAliasing(fd)
    fdsAliases(fd)
  })

  def expressionAliasing(expr: Expr): Set[Identifier] = {
    val fds: Set[FunDef] = dependencies(expr).collect{ case (fd: FunDef) => fd }
    fds.foreach(fd => functionAliasing(fd)) //make sure each fd is in the fdSAliases map
    currentExpressionAliasing(expr, fdsAliases, new AliasingGraph)
  }


  /** abstraction for function without body
    *
    * This is the abstraction used in the analysis for a function that does
    * not have an implementation (HOF or external function). You can override
    * to choose the abstraction that suits you the best.
    * 
    * The default abstraction is to conservatively assume a function invocation with
    * unknown implementation can alias any of its parameters.
    * In Stainless, with the global assumption of non-aliasing, this is too conservative, and
    * you can use the StainlessAliasAnalysis class that override this behaviour with a less
    * conservative approach that assumes no aliasing.
    *
    * This default choice is made as this enables a correct alias analysis, while the abstraction
    * used by Stainless relies on systematically checking and restricting aliasing everywhere.
    */
  def functionAbstraction(ft: FunctionType): Seq[Int] = ft.from.zipWithIndex.map(_._2)


  private def computeFunctionAliasing(from: FunDef): Set[Identifier] = {
    val fds: Set[FunDef] = dependencies(from).collect{ case (fd: FunDef) => fd } + from

    val aliases: MutableMap[FunDef, Set[Identifier]] = fdsAliases.map(p => p)//essentially cloning

    var aliasesSnapshot = aliases.toMap
    do {
      aliasesSnapshot = aliases.toMap
      //could optimize by keeping a call graph dependency, and only re-run on dependencies
      for(fd <- fds) {
        fd.body match {
          case None => {
            val ft: FunctionType = fd.typed.functionType
            val ftAliases: Seq[Int] = functionAbstraction(ft)
            aliases(fd) = fd.params.zipWithIndex.filter(p => ftAliases.contains(p._2)).map(_._1.id).toSet
          }
          case Some(body) => {
            val freeVars = variablesOf(body)
            val paramIds = fd.params.map(_.id)
            val aliasesSuperset = freeVars ++ paramIds.toSet
            aliases(fd) = currentExpressionAliasing(body, aliases, new AliasingGraph).filter(aliasesSuperset.contains _)
          }
        }
      }
    } while(aliases != aliasesSnapshot)

    aliases.foreach{
      case (fd, aliases) => fdsAliases(fd) = aliases
    }
    fdsAliases(from)
  }


  /*
   * Graph for local aliasing inside an expression/function body
   */
  private class AliasingGraph {
    private val aliases: MutableMap[Identifier, Set[Identifier]] = MutableMap.empty
    
    /* add an alias, bidirectional */
    def addAlias(id: Identifier, alias: Identifier): Unit = {
      aliases(id) = aliases.getOrElse(id, Set(id)) + alias
      aliases(alias) = aliases.getOrElse(alias, Set(alias)) + id
    }

    def addAliases(aliases: Set[Identifier]): Unit = {
      for(a1 <- aliases)
        for(a2 <- aliases)
          addAlias(a1, a2)
    }

    def apply(id: Identifier): Set[Identifier] = aliases.getOrElse(id, Set(id))

    override def toString: String = aliases.toString

    //TODO: need a notion of alias in only one direction, for when an id points to a field of an object.
  }

  /*
   * returns possible aliases for the value taken by expr.
   * depends on the current known aliases for each FunDef, so it keeps
   * being refined during fixpoint computation
   * The currentAliases should not be mutated in the body (this is a mutable map
   * to avoid a costly copy to an immutable map), and is the current computed
   * aliases for each function.
   *
   * The aliases are not necessarly defined in the outer scope, if the expression is
   * a sequence of lets, the possible aliases are defined as all the ids defined
   * along the way. For example, let a = x in let b = a in b, would return the possible aliases
   * of {a, b, x} for the result, with x not defined (deduced from the assignment to a) and a and
   * b defined inline.
   *
   * Using AliasingGraph, which has mutable state, means that the identifier will not maintain
   * proper scoping. Maybe this is an issue and we should use an immutable graph?
   */
  private def currentExpressionAliasing(
    expr: Expr, currentAliases: MutableMap[FunDef, Set[Identifier]], localAliases: AliasingGraph
  ): Set[Identifier] = {
  
    def rec(e: Expr): Set[Identifier] = e match {
      //if localAliases contains an id, it automatically maps it to itself at least
      case Variable(v) => localAliases(v)
      case Let(id, e, b) => {
        val eas = rec(e)
        eas.foreach(ea => localAliases.addAlias(id, ea))
        rec(b)
      }
      case LetVar(id, e, b) => {
        val eas = rec(e)
        eas.foreach(ea => localAliases.addAlias(id, ea))
        rec(b)
      }
      case MatchExpr(e, cses) => {
        val eas = rec(e)
        val subBinders = cses.flatMap(mc => mc.pattern.binders).toSet
        localAliases.addAliases(subBinders) //all binders are aliases to each other
        eas.foreach(ea => subBinders.foreach(nid => localAliases.addAlias(ea, nid)))
        cses.toSet.flatMap((cse: MatchCase) => rec(cse.rhs))
      }
      case IfExpr(c, t, e) => {
        rec(c)
        rec(t) ++ rec(e)
      }
      case AsInstanceOf(e, _) => rec(e)
      case FunctionInvocation(tfd, args) => {
        val fdAliases: Set[Identifier] = currentAliases.getOrElse(tfd.fd, Set())
        val (paramAliases, externalAliases) = fdAliases.partition(alias => tfd.fd.params.exists(_.id == alias))
        val fiAliases: Set[Identifier] = paramAliases.flatMap(fdAlias => {
          val aliasedArg = args(tfd.fd.params.indexWhere(_.id == fdAlias))
          rec(aliasedArg)
        })
        fiAliases ++ externalAliases
      }

      case Application(lambda, args) => {
        val ft: FunctionType = lambda.getType.asInstanceOf[FunctionType]
        val ftAliases: Seq[Int] = functionAbstraction(ft)
        val aliasedArgs: Set[Expr] = args.zipWithIndex.filter(p => ftAliases.contains(p._2)).map(_._1).toSet
        rec(lambda)
        aliasedArgs.flatMap(rec)
      }

      //this case only makes sense to update the localAliases map
      case Assignment(id, v) => {
        val vAliases = rec(v)
        vAliases.foreach(alias => localAliases.addAlias(id, alias))
        Set()
      }
      case Block(es, e) => {
        //this takes advantage of mutability of the local aliasing for assignments
        es.foreach(rec)
        rec(e)
      }
      case CaseClass(_, args) => {
        args.toSet.flatMap((arg: Expr) => rec(arg))
      }
      case CaseClassSelector(_, obj, _) => {
        rec(obj)
      }
      case FiniteArray(elems, default, length) => {
        rec(length)
        val es: Seq[Expr] = elems.values.toSeq ++ default
        es.flatMap(rec).toSet
      }

      //we consider that any other operation not handled above essentially wraps the
      //expression into a new fresh value, so will not have any alias
      //we still have to run rec to the sub-expressions, to properly update the
      //local aliasing with assignments.
      case Operator(es, _) => {
        es.foreach(rec)
        Set()
      }
    }

    rec(expr)
  }


  //for a given id, compute the identifiers that alias it or some part of the object refered by id
  //private def computeLocalAliases(id: Identifier, body: Expr): Set[Identifier] = {
  //  def pre(expr: Expr, ids: Set[Identifier]): Set[Identifier] = expr match {
  //    case l@Let(i, Variable(v), _) if ids.contains(v) => ids + i
  //    case m@MatchExpr(Variable(v), cses) if ids.contains(v) => {
  //      val newIds = cses.flatMap(mc => mc.pattern.binders)
  //      ids ++ newIds
  //    }
  //    case e => ids
  //  }
  //  def combiner(e: Expr, ctx: Set[Identifier], ids: Seq[Set[Identifier]]): Set[Identifier] = ctx ++ ids.toSet.flatten + id
  //  val res = preFoldWithContext(pre, combiner)(body, Set(id))
  //  res
  //}

}

/** Stainless specific alias analysis
  *
  * This override the AliasAnalysis behaviour to apply
  * in the case of Stainless. That means, with global assumption
  * that functions have no aliasing effects. We still do proper
  * alias analysis of function bodies, but function without known
  * implementation are considered as alias-free, and function
  * invocation are not followed (assuming no-aliasing as well).
  */
class StainlessAliasAnalysis extends AliasAnalysis {
  override def functionAbstraction(ft: FunctionType): Seq[Int] = Seq()

  //TODO: find a way to override the behaviour to not go inter-modular (return empty set of dependencies for function invocations)
}
