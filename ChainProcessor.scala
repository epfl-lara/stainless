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

  ChainBuilder.init
  ChainComparator.init

  def run(problem: Problem): (TraversableOnce[Result], TraversableOnce[Problem]) = {
    reporter.info("- Running ChainProcessor")
    val allChainMap       : Map[FunDef, Set[Chain]] = problem.funDefs.map(funDef => funDef -> ChainBuilder.run(funDef)).toMap
    reporter.info("- Computing all possible Chains")
    val possibleChainMap  : Map[FunDef, Set[Chain]] = allChainMap.mapValues(chains => chains.filter(chain => isSAT(And(chain.loop()))))
    reporter.info("- Collecting re-entrant Chains")
    val reentrantChainMap : Map[FunDef, Set[Chain]] = possibleChainMap.mapValues(chains => chains.filter(chain => isSAT(And(chain reentrant chain))))

    // We build a cross-chain map that determines which chains can reenter into another one after a loop.
    // Note: We are also checking reentrance SAT here, so again, we negate the formula!
    reporter.info("- Computing cross-chain map")
    val crossChains       : Map[Chain, Set[Chain]]  = possibleChainMap.map({ case (funDef, chains) =>
      val reentrant = reentrantChainMap(funDef)
      val reentrantPairs = reentrant.map(chain => chain -> Set(chain))
      val crosswise = (chains -- reentrant).map(chain => chain -> {
        reentrant.filter(other => isSAT(And(chain reentrant other)))
      })
      reentrantPairs ++ crosswise
    }).flatten.toMap

    val validChainMap     : Map[FunDef, Set[Chain]] = possibleChainMap.map({ case (funDef, chains) => funDef -> chains.filter(crossChains(_).nonEmpty) })

    // We use the cross-chains to build chain clusters. For each cluster, we must prove that the SAME argument
    // decreases in each of the chains in the cluster!
    reporter.info("- Building initial cluster estimation by fix-point iteration")
    val generalClusters : Map[FunDef, Set[Set[Chain]]] = {
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

      validChainMap.map({ case (funDef, chains) => funDef -> build(chains) })
    }

    reporter.info("- Trimming down to final clusters")
    val clusters : Map[FunDef, Set[Set[Chain]]] = generalClusters.map({ case (funDef, clusters) =>
      funDef -> clusters.map(cluster => cluster.toSeq.sortBy(_.size).foldLeft(Set[Chain]())({ case (acc, chain) =>
        val chainElements : Set[Relation] = chain.chain.toSet
        val seenElements  : Set[Relation] = acc.map(_.chain).flatten.toSet
        if (chainElements -- seenElements nonEmpty) acc + chain else acc
      })).filter(_.nonEmpty)
    })

    reporter.info("- Strengthening postconditions")
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

    def clear(clusters: ClusterMap, gen: FormulaGenerator): ClusterMap = {
      val formulas = clusters.map({ case (fd, clusters) =>
        (fd, clusters.map(cluster => cluster -> gen(fd, cluster)))
      })

      initSolvers // add structural size functions to solver
      formulas.map({ case (fd, clustersWithFormulas) =>
        fd -> clustersWithFormulas.filter({ case (cluster, formula) => !isAlwaysSAT(formula) }).map(_._1)
      })
    }

    reporter.info("- Searching for structural size decrease")
    val sizeCleared : ClusterMap = clear(clusters, (fd, cluster) => {
      val (e1, e2s) = buildLoops(fd, cluster)
      ChainComparator.sizeDecreasing(e1, e2s)
    })

    reporter.info("- Searching for numeric convergence")
    val numericCleared : ClusterMap = clear(sizeCleared, (fd, cluster) => {
      val (e1, e2s) = buildLoops(fd, cluster)
      ChainComparator.numericConverging(e1, e2s, cluster, checker)
    })

    val (okPairs, nokPairs) = numericCleared.partition(_._2.isEmpty)
    val nok = nokPairs.map(_._1).toSet
    val (ok, transitiveNok) = okPairs.map(_._1).partition({ fd =>
      checker.program.transitiveCallees(fd) intersect nok isEmpty
    })
    val allNok = nok ++ transitiveNok
    val newProblems = if (allNok nonEmpty) List(Problem(allNok)) else Nil
    (ok.map(Cleared(_)), newProblems)
  }
}
