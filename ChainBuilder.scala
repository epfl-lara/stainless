package leon
package termination

import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Common._

import scala.collection.mutable.{Map => MutableMap}

object ChainID {
  private var counter: Int = 0
  def get: Int = {
    counter = counter + 1
    counter
  }
}

final case class Chain(chain: List[Relation]) {
  val id = ChainID.get

  override def equals(obj: Any): Boolean = obj.isInstanceOf[Chain] && obj.asInstanceOf[Chain].id == id
  override def hashCode(): Int = id

  def funDef  : FunDef                    = chain.head.funDef
  def funDefs : Set[FunDef]               = chain.map(_.funDef).toSet

  lazy val size: Int = chain.size

  def loop(initialSubst: Map[Identifier, Expr] = Map(), finalSubst: Map[Identifier, Expr] = Map()) : Seq[Expr] = {
    def rec(relations: List[Relation], subst: Map[Identifier, Expr]): Seq[Expr] = relations match {
      case Relation(_, path, FunctionInvocation(tfd, args)) :: Nil =>
        assert(tfd.fd == funDef)
        val newPath = path.map(replaceFromIDs(subst, _))
        val equalityConstraints = if (finalSubst.isEmpty) Seq() else {
          val newArgs = args.map(replaceFromIDs(subst, _))
          (tfd.params.map(arg => finalSubst(arg.id)) zip newArgs).map(p => Equals(p._1, p._2))
        }
        newPath ++ equalityConstraints
      case Relation(_, path, FunctionInvocation(tfd, args)) :: xs =>
        val formalArgs = tfd.params.map(_.id)
        val freshFormalArgVars = formalArgs.map(_.freshen.toVariable)
        val formalArgsMap: Map[Identifier, Expr] = (formalArgs zip freshFormalArgVars).toMap
        val (newPath, newArgs) = (path.map(replaceFromIDs(subst, _)), args.map(replaceFromIDs(subst, _)))
        val constraints = newPath ++ (freshFormalArgVars zip newArgs).map(p => Equals(p._1, p._2))
        constraints ++ rec(xs, formalArgsMap)
      case Nil => sys.error("Empty chain shouldn't exist by construction")
    }

    val subst : Map[Identifier, Expr] = if (initialSubst.nonEmpty) initialSubst else {
      funDef.params.map(arg => arg.id -> arg.toVariable).toMap
    }
    val Chain(relations) = this
    rec(relations, subst)
  }

  def reentrant(other: Chain) : Seq[Expr] = {
    assert(funDef == other.funDef)
    val bindingSubst : Map[Identifier, Expr] = funDef.params.map({
      arg => arg.id -> arg.id.freshen.toVariable
    }).toMap
    val firstLoop = loop(finalSubst = bindingSubst)
    val secondLoop = other.loop(initialSubst = bindingSubst)
    firstLoop ++ secondLoop
  }

  def inlined: TraversableOnce[Expr] = {
    def rec(list: List[Relation], mapping: Map[Identifier, Expr]): List[Expr] = list match {
      case Relation(_, _, FunctionInvocation(fd, args)) :: xs =>
        val mappedArgs = args.map(replaceFromIDs(mapping, _))
        val newMapping = fd.params.map(_.id).zip(mappedArgs).toMap
        // We assume we have a body at this point. It would be weird to have gotten here without one...
        val expr = hoistIte(expandLets(matchToIfThenElse(fd.body.get)))
        val inlinedExpr = replaceFromIDs(newMapping, expr)
        inlinedExpr:: rec(xs, newMapping)
      case Nil => Nil
    }

    val body = hoistIte(expandLets(matchToIfThenElse(funDef.body.get)))
    body :: rec(chain, funDef.params.map(arg => arg.id -> arg.toVariable).toMap)
  }
}

class ChainBuilder(relationBuilder: RelationBuilder) {

  private val chainCache : MutableMap[FunDef, Set[Chain]] = MutableMap()

  def run(funDef: FunDef): Set[Chain] = chainCache.get(funDef) match {
    case Some(chains) => chains
    case None => {
      // Note that this method will generate duplicate cycles (in fact, it will generate all list representations of a cycle)
      def chains(partials: List[(Relation, List[Relation])]): List[List[Relation]] = if (partials.isEmpty) Nil else {
        // Note that chains in partials are reversed to profit from O(1) insertion
        val (results, newPartials) = partials.foldLeft(List[List[Relation]](),List[(Relation, List[Relation])]())({
          case ((results, partials), (first, chain @ Relation(_, _, FunctionInvocation(tfd, _)) :: xs)) =>
            val cycle = relationBuilder.run(tfd.fd).contains(first)
            // reverse the chain when "returning" it since we're working on reversed chains
            val newResults = if (cycle) chain.reverse :: results else results

            // Partial chains can fall back onto a transition that was already taken (thus creating a cycle
            // inside the chain). Since this cycle will be discovered elsewhere, such partial chains should be
            // dropped from the partial chain list
            val transitions = relationBuilder.run(tfd.fd) -- chain.toSet
            val newPartials = transitions.map(transition => (first, transition :: chain)).toList

            (newResults, partials ++ newPartials)
          case (_, (_, Nil)) => scala.sys.error("Empty partial chain shouldn't exist by construction")
        })

        results ++ chains(newPartials)
      }

      val initialPartials = relationBuilder.run(funDef).map(r => (r, r :: Nil)).toList
      val result = chains(initialPartials).map(Chain(_)).toSet
      chainCache(funDef) = result
      result
    }
  }
}
