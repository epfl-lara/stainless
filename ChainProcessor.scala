package leon
package termination

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Common._
import purescala.Extractors._
import purescala.Definitions._

class ChainProcessor(checker: TerminationChecker) extends Processor(checker) with Solvable {

  val name: String = "Chain Processor"

  def run(problem: Problem) = {
    val allChainMap : Map[FunDef, Set[Chain]] = problem.funDefs.map(funDef => funDef -> ChainBuilder.run(funDef)).toMap
    val allChains   : Set[Chain]              = allChainMap.values.flatten.toSet

    // We check that loops can reenter themselves after a run. If not, then this is not a chain (since it will
    // enter another chain and their conjunction is contained elsewhere in the chains set)
    // Note: We are checking reentrance SAT, not looking for a counter example so we negate the formula!
    val validChains : Set[Chain]              = allChains.filter(chain => !solve(Not(And(chain reentrant chain))).isValid)
    val chainMap    : Map[FunDef, Set[Chain]] = allChainMap.mapValues(chains => chains intersect validChains)

    // We build a cross-chain map that determines which chains can reenter into another one after a loop.
    // Note: We are also checking reentrance SAT here, so again, we negate the formula!
    val crossChains : Map[Chain, Set[Chain]] = chainMap.map({ case (funDef, chains) =>
      chains.map(chain => chain -> (chains - chain).filter(other => !solve(Not(And(chain reentrant other))).isValid))
    }).flatten.toMap

    // We use the cross-chains to build chain clusters. For each cluster, we must prove that the SAME argument
    // decreases in each of the chains in the cluster!
    val clusters : Map[FunDef, Set[Set[Chain]]] = {
      def cluster(set: Set[Chain]): Set[Chain] = {
        set ++ set.map(crossChains(_)).flatten
      }

      def fix[A](f: A => A, a: A): A = {
        val na = f(a)
        if (a == na) a else fix(f, na)
      }

      def filterClusters(all: List[Set[Chain]]): List[Set[Chain]] = if (all.isEmpty) Nil else {
        val newCluster = all.head
        val rest = all.tail.filter(set => !set.subsetOf(newCluster))
        newCluster :: filterClusters(rest)
      }

      def build(chains: Set[Chain]): Set[Set[Chain]] = {
        val allClusters = chains.map(chain => fix(cluster, Set(chain)))
        filterClusters(allClusters.toList.sortBy(- _.size)).toSet
      }

      chainMap.map({ case (funDef, chains) => funDef -> build(chains) })
    }

    strengthenPostconditions(problem.funDefs)

    def buildLoops(fd: FunDef, cluster: Set[Chain]): (Expr, Seq[(Seq[Expr], Expr)]) = {
      val e1 = Tuple(fd.args.map(_.toVariable))
      val e2s = cluster.toSeq.map({ chain =>
        val freshArgs : Seq[Expr] = fd.args.map(arg => arg.id.freshen.toVariable)
        val finalBindings = (fd.args.map(_.id) zip freshArgs).toMap
        val path = chain.loop(finalSubst = finalBindings)
        path -> Tuple(freshArgs)
      })

      (e1, e2s)
    }

    type ClusterMap = Map[FunDef, Set[Set[Chain]]]
    type FormulaGenerator = (FunDef, Set[Chain]) => Expr

    def clear(clusters: ClusterMap, gen: FormulaGenerator): ClusterMap = clusters.map({ case (fd, clusters) =>
      val remaining = clusters.filter(cluster => !solve(gen(fd, cluster)).isValid)
      fd -> remaining
    })

    val sizeCleared : ClusterMap = clear(clusters, (fd, cluster) => {
      val (e1, e2s) = buildLoops(fd, cluster)
      ChainComparator.sizeDecreasing(e1, e2s)
    })

    val numericCleared : ClusterMap = clear(sizeCleared, (fd, cluster) => {
      val (e1, e2s) = buildLoops(fd, cluster)
      ChainComparator.numericConverging(e1, e2s, cluster, checker)
    })

    val (okPairs, nokPairs) = numericCleared.partition(_._2.isEmpty)
    val newProblems = if (nokPairs nonEmpty) List(Problem(nokPairs.map(_._1).toSet)) else Nil
    (okPairs.map(p => Cleared(p._1)), newProblems)
  }
}
