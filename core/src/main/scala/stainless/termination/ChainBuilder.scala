/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap}

trait ChainBuilder extends RelationBuilder { self: Strengthener with OrderingRelation =>

  import checker._
  import program.trees._
  import program.symbols.{given, _}
  import program.trees.exprOps._

  case class Chain(relations: List[Relation]) {
    override def toString: String = {
      import stainless.utils.StringUtils.indent
      s"Chain(${relations.map(_.toString).map(indent(_, 2)).mkString("\n", ",\n", "\n")})" +
      s"\nLoop(${loop})"
    }

    private lazy val identifier: Map[(Relation, Relation), Int] = {
      (relations zip (relations.tail :+ relations.head)).view.groupBy(p => p).view.mapValues(_.size).toMap
    }

    override def equals(obj: Any): Boolean = obj match {
      case (chain: Chain) => chain.identifier == identifier
      case _              => false
    }

    override def hashCode: Int = identifier.hashCode()

    lazy val fd: FunDef = relations.head.fd
    lazy val fds: Set[FunDef] = relations.map(_.fd).toSet

    lazy val size: Int = relations.size

    lazy val loop: (Path, Seq[Expr]) = {
      val bigRel = relations.reduce(_ compose _)
      (bigRel.path, bigRel.call.args)
    }

    lazy val cycles: Seq[List[Relation]] = relations.indices.map { index =>
      val (start, end) = relations.splitAt(index)
      end ++ start
    }

    def compose(that: Chain): Set[Chain] = {
      val map = relations.zipWithIndex
        .map(p => p._1.call.tfd.fd -> ((p._2 + 1) % relations.size))
        .groupBy(_._1)
        .view.mapValues(_.map(_._2))
        .toMap
      val tmap = that.relations.zipWithIndex.map(p => p._1.fd -> p._2).groupBy(_._1).view.mapValues(_.map(_._2)).toMap
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
  }

  protected type ChainSignature = (FunDef, Set[RelationSignature])

  protected def funDefChainSignature(funDef: FunDef): ChainSignature = {
    funDef -> (transitiveCallees(funDef) + funDef).map(funDefRelationSignature)
  }

  private val chainCache: MutableMap[FunDef, (Set[FunDef], Set[Chain], ChainSignature)] = MutableMap.empty

  def getChains(funDef: FunDef): (Set[FunDef], Set[Chain]) = chainCache.get(funDef) match {
    case Some((subloop, chains, signature)) if signature == funDefChainSignature(funDef) => subloop -> chains
    case _ => {
      def chains(seen: Set[FunDef], chain: List[Relation]): (Set[FunDef], Set[Chain]) = {
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
