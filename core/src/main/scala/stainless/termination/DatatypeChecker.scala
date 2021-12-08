/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

class DatatypeChecker(val checker: TerminationChecker) {
  import checker._
  import program._
  import program.trees._
  import program.symbols.{given, _}

  private class DependencyFinder(deps: MutableSet[Identifier]) extends ConcreteStainlessSelfTreeTraverser {
    override def traverse(e: Expr): Unit = e match {
      case FunctionInvocation(id, _, _) =>
        deps += id
        deps ++= dependencies(id)
        super.traverse(e)
      case _ =>
        super.traverse(e)
    }

    override def traverse(tpe: Type): Unit = tpe match {
      case ADTType(id, _) =>
        deps += id
        deps ++= dependencies(id)
        getSort(id).invariant.foreach(inv => deps ++= dependencies(inv.id))
        super.traverse(tpe)
      case _ =>
        super.traverse(tpe)
    }
  }

  private val dependencyCache: MutableMap[Identifier, MutableSet[Identifier]] = MutableMap.empty
  private def dependencies(id: Identifier): Set[Identifier] = dependencyCache.get(id) match {
    case Some(ids) => ids.toSet
    case None =>
      val deps: MutableSet[Identifier] = MutableSet.empty
      val finder = new DependencyFinder(deps)
      dependencyCache(id) = deps
      lookupFunction(id) match {
        case Some(fd) => finder.traverse(fd)
        case None     => finder.traverse(getSort(id))
      }
      deps.toSet
  }

  def check(fd: FunDef): Option[NonTerminating] = {
    val deps = dependencies(fd.id)
    val sorts = deps.flatMap(lookupSort(_))
    val notWellFormed = sorts.filter { sort =>
      def isPositive(tpe: Type, pol: Boolean, seen: Set[ADTType]): Boolean = tpe match {
        case ADTType(sort.id, _) if !pol => false
        case adt: ADTType if seen(adt)   => true
        case adt: ADTType =>
          adt.getSort.constructors.forall(tc => tc.fields.map(_.tpe).forall(isPositive(_, pol, seen + adt)))
        case FunctionType(from, to) => from.forall(isPositive(_, !pol, seen)) && isPositive(to, pol, seen)
        case NAryType(tps, _)       => tps.forall(isPositive(_, pol, seen))
      }

      !isPositive(ADTType(sort.id, sort.typeArgs), true, Set.empty)
    }

    if (notWellFormed.isEmpty) None else Some(NotWellFormed(notWellFormed))
  }
}
