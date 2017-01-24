/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap}

trait ChainBuilder extends RelationBuilder { self: Strengthener with OrderingRelation =>

  import checker._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._

  case class Chain(relations: List[Relation]) {

    private lazy val identifier: Map[(Relation, Relation), Int] = {
      (relations zip (relations.tail :+ relations.head)).groupBy(p => p).mapValues(_.size)
    }

    override def equals(obj: Any): Boolean = obj match {
      case (chain: Chain) => chain.identifier == identifier
      case _ => false
    }

    override def hashCode: Int = identifier.hashCode()

    lazy val fd  : FunDef      = relations.head.fd
    lazy val fds : Set[FunDef] = relations.map(_.fd).toSet

    lazy val size: Int = relations.size

    private lazy val inlining : Seq[(Seq[ValDef], Expr)] = {
      def rec(list: List[Relation], funDef: TypedFunDef, args: Seq[Expr]): Seq[(Seq[ValDef], Expr)] = list match {
        case Relation(_, _, FunctionInvocation(id, tps, nextArgs), _) :: xs =>
          val tfd = getFunction(id, tps.map(funDef.instantiate))
          val subst = funDef.paramSubst(args)
          val expr = replaceFromSymbols(subst, hoistIte(expandLets(matchToIfThenElse(tfd.body.get))))
          val mappedArgs = nextArgs.map(e => replaceFromSymbols(subst, tfd.instantiate(e)))

          (tfd.params, expr) +: rec(xs, tfd, mappedArgs)
        case Nil => Seq.empty
      }

      val body = hoistIte(expandLets(matchToIfThenElse(fd.body.get)))
      (fd.params, body) +: rec(relations, fd.typed, fd.params.map(_.toVariable))
    }

    lazy val finalParams : Seq[ValDef] = inlining.last._1

    def loop(initialArgs: Seq[ValDef] = Seq.empty, finalArgs: Seq[ValDef] = Seq.empty): Path = {
      def rec(relations: List[Relation], funDef: TypedFunDef, subst: Map[ValDef, Expr]): Path = {
        val Relation(_, path, FunctionInvocation(id, tps, args), _) = relations.head
        val tfd = getFunction(id, tps.map(funDef.instantiate))
        val instPath = path.instantiate(funDef.tpSubst)

        val freshBindings = instPath.bound.map(vd => vd.freshen)
        val freshSubst = (instPath.bound zip freshBindings).toMap
        val newSubst = subst ++ freshSubst.mapValues(_.toVariable)

        val newPath = instPath.map(freshSubst, replaceFromSymbols(newSubst, _))

        lazy val newArgs = args.map(e => replaceFromSymbols(newSubst, funDef.instantiate(e)))

        newPath merge (relations.tail match {
          case Nil =>
            Path.empty withBindings (finalArgs zip newArgs)
          case xs =>
            val freshParams = tfd.params.map(_.freshen)
            val recPath = rec(xs, tfd, (tfd.params zip freshParams.map(_.toVariable)).toMap)
            Path.empty withBindings (freshParams zip newArgs) merge recPath
        })
      }

      rec(relations, fd.typed, (fd.params zip initialArgs.map(_.toVariable)).toMap)
    }

    /*
    def reentrant(other: Chain) : Seq[Expr] = {
      assert(funDef == other.funDef)
      val bindingSubst = funDef.params.map(vd => vd.id -> vd.id.freshen).toMap
      val firstLoop = loop(finalSubst = bindingSubst)
      val secondLoop = other.loop(initialSubst = bindingSubst)
      firstLoop ++ secondLoop
    }
    */

    lazy val cycles : Seq[List[Relation]] = relations.indices.map { index =>
      val (start, end) = relations.splitAt(index)
      end ++ start
    }

    def compose(that: Chain): Set[Chain] = {
      val map = relations.zipWithIndex.map(p => p._1.call.tfd.fd -> ((p._2 + 1) % relations.size)).groupBy(_._1).mapValues(_.map(_._2))
      val tmap = that.relations.zipWithIndex.map(p => p._1.fd -> p._2).groupBy(_._1).mapValues(_.map(_._2))
      val keys = map.keys.toSet & tmap.keys.toSet

      for {
        fd <- keys
        i1 <- map(fd)
        (start1, end1) = relations.splitAt(i1)
        called = if (start1.isEmpty) relations.head.fd else start1.last.call.tfd.fd
        i2 <- tmap(called)
        (start2, end2) = that.relations.splitAt(i2)
      } yield Chain(start1 ++ end2 ++ start2 ++ end1)
    }

    lazy val inlined: Seq[Expr] = inlining.map(_._2)
  }


  protected type ChainSignature = (FunDef, Set[RelationSignature])

  protected def funDefChainSignature(funDef: FunDef): ChainSignature = {
    funDef -> (transitiveCallees(funDef) + funDef).map(funDefRelationSignature)
  }

  private val chainCache : MutableMap[FunDef, (Set[FunDef], Set[Chain], ChainSignature)] = MutableMap.empty

  def getChains(funDef: FunDef): (Set[FunDef], Set[Chain]) = chainCache.get(funDef) match {
    case Some((subloop, chains, signature)) if signature == funDefChainSignature(funDef) => subloop -> chains
    case _ => {
      def chains(seen: Set[FunDef], chain: List[Relation]) : (Set[FunDef], Set[Chain]) = {
        val Relation(_, _, FunctionInvocation(id, _, _), _) :: _ = chain
        val fd = getFunction(id)

        if (!transitivelyCalls(fd, funDef)) {
          Set.empty[FunDef] -> Set.empty[Chain]
        } else if (fd == funDef) {
          Set.empty[FunDef] -> Set(Chain(chain.reverse))
        } else if (seen(fd)) {
          Set(fd) -> Set.empty[Chain]
        } else {
          val results = getRelations(fd).map(r => chains(seen + fd, r :: chain))
          val (funDefs, allChains) = results.unzip
          (funDefs.flatten, allChains.flatten)
        }
      }

      val results = getRelations(funDef).map(r => chains(Set.empty, r :: Nil))
      val (funDefs, allChains) = results.unzip

      val loops = funDefs.flatten
      val resChains = allChains.flatten

      chainCache(funDef) = (loops, resChains, funDefChainSignature(funDef))

      loops -> resChains
    }
  }
}
