/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait DatatypeChecker {
  val checker: TerminationChecker
  import checker._
  import program._
  import program.trees._
  import program.symbols._

  private class DependencyFinder(deps: MutableSet[Identifier]) extends TreeTraverser {
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
        getADT(id).invariant.foreach(inv => deps ++= dependencies(inv.id))
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
        case None => getADT(id) match {
          case sort: ADTSort =>
            finder.traverse(sort)
            sort.constructors.foreach(finder.traverse)
          case adt =>
            finder.traverse(adt)
        }
      }
      deps.toSet
  }

  def check(fd: FunDef): Option[NonTerminating] = {
    val deps = dependencies(fd.id)
    val adts = deps.flatMap(lookupADT(_))
    val notWellFormed = adts.filter {
      case cons: ADTConstructor =>
        def isPositive(tpe: Type, pol: Boolean, seen: Set[ADTType]): Boolean = tpe match {
          case ADTType(cons.id, _) if !pol => false
          case adt: ADTType if seen(adt) => true
          case adt: ADTType => adt.getADT match {
            case tsort: TypedADTSort => tsort.constructors.forall(tc => isPositive(tc.toType, pol, seen + adt))
            case tcons: TypedADTConstructor => tcons.fieldsTypes.forall(isPositive(_, pol, seen + adt))
          }
          case FunctionType(from, to) => from.forall(isPositive(_, !pol, seen)) && isPositive(to, pol, seen)
          case NAryType(tps, _) => tps.forall(isPositive(_, pol, seen))
        }

        !isPositive(cons.typed.toType, true, Set.empty)

      // Note that sort constructors are dependencies of sorts so they will
      // belong to the `adts` list anyway
      case _ => false
    }

    if (notWellFormed.isEmpty) None else Some(NotWellFormed(notWellFormed))
  }
}
