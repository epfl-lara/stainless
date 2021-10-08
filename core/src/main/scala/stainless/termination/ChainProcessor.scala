/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

class ChainProcessor(override val checker: ProcessingPipeline)
                    // Alias for checker, as we cannot use it to define ordering
                    (override val chker: checker.type)
                    (override val ordering: OrderingRelation with ChainBuilder with Strengthener with StructuralSize {
                      val checker: chker.type
                    })
  extends OrderingProcessor("Chain Processor", checker, ordering) {

  def this(chker: ProcessingPipeline,
           ordering: OrderingRelation with ChainBuilder with Strengthener with StructuralSize {
             val checker: chker.type
           }) =
    this(chker)(chker)(ordering)

  val depth: Int = 1

  import checker._
  import ordering._
  import checker.context._
  import checker.program.trees._
  import checker.program.symbols.{given, _}

  private def lessThan(e1s: Seq[(Path, Expr)], e2: Expr): Seq[(Expr, Expr, Expr => Expr)] =
    flatTypesPowerset(e2.getType).toSeq.map(recons => (andJoin(e1s.map {
      case (path, e1) => path implies ordering.lessThan(Seq(recons(e1)), Seq(recons(e2)))
    }), recons(e2), recons))

  def run(problem: Problem): Option[Seq[Result]] = timers.termination.processors.chains.run {
    strengthenPostconditions(problem.funSet)
    strengthenApplications(problem.funSet)

    val api = getAPI

    reporter.debug("- Running ChainBuilder")
    val chainsMap = problem.funSet.map { funDef =>
      funDef -> getChains(funDef)
    }.toMap

    val loopPoints = chainsMap.foldLeft(Set.empty[FunDef]) {
      case (set, (fd, (fds, chains))) => set ++ fds
    }

    if (loopPoints.size > 1) {
      reporter.debug("-+> Multiple looping points, can't build chain proof")
      return None
    }

    val bases: Seq[FunDef] =
      {if (loopPoints.nonEmpty) loopPoints
      else chainsMap.collect {
        case (fd, (fds, chains)) if chains.nonEmpty => fd
      }}.toList

    findDecrease(bases,chainsMap,checker.program.symbols) match {
      case (cs, Some(base), Some(reconstr)) =>
        annotateChains(cs,base,reconstr)
        Some(problem.funDefs.map { fd =>
          measureCache.get(fd) match {
            case Some(measure) =>
              val inductiveLemmas =
                Some((ordering.getPostconditions, ordering.insertedApps))
              Cleared(fd, Some(measure), inductiveLemmas)
            case None =>
              throw FailedMeasureInference(fd,
                s"No measure annotated in function `${fd.id}` which was cleared in chain processor.")
          }
        })
      case (Seq(), _, _) =>
        None
    }
  }

  def findDecrease(bases: Seq[FunDef], chainsMap: Map[FunDef,(Set[FunDef], Set[Chain])], syms: Symbols): (Seq[Chain], Option[FunDef], Option[Expr => Expr]) = {
    val depth: Int = 1 // Number of unfoldings
    val api = getAPI

    def solveIter(i: Int,allChains: Set[Chain],cs: Set[Chain],base: FunDef): (Set[Chain], Option[Expr => Expr]) = {
      reporter.debug("-+> Iteration #" + i)
      if(i < 0) (cs,None)
      else {
        val e1s = cs.toSeq.map { chain =>
          val (path, args) = chain.loop
          (path, tupleWrap(args))
        }
        val e2 = tupleWrap(base.params.map(_.toVariable))
        val formulas = lessThan(e1s, e2)
        val decreases: Option[(Expr, Expr, Expr => Expr)] = formulas.find { case (query, _, _) =>
          api.solveVALID(query).contains(true)
        }
        if (decreases.isDefined) (cs,Some(decreases.get._3))
        else {
          val newChains = cs.flatMap(c1 => allChains.flatMap(c2 => c1 compose c2))
          solveIter(i-1,allChains,newChains, base)
        }
      }
    }

    def solveBase(bases: Seq[FunDef]): (Seq[Chain], Option[FunDef], Option[Expr => Expr]) = bases match {
      case base :: bs =>
        val chains = chainsMap(base)._2
        val allChains = chainsMap(base)._2
        reporter.debug("- Searching for size decrease")
        val (cs,reconstr) = solveIter(depth, allChains,chains, base)
        if(reconstr.isDefined) (cs.toSeq, Some(base), reconstr)
        else solveBase(bs)
      case Nil => (Seq(), None, None)
    }

    solveBase(bases)
  }

  /*
   * Measure annotation for the chain processor
   */
  private val measureCache: MutableMap[FunDef, Expr] = MutableMap.empty

  def annotateChains(cs: Seq[Chain],base: FunDef,recons: Expr => Expr): Unit = {
    /* Stores for a function f an index i the measure expressions
     holding for those values leaving the chains in i steps.
     If i = -1 then the value loops. */
    val annotationMap: MutableMap[(FunDef,Int),Seq[(Expr,Expr)]] =
      MutableMap.empty[(FunDef,Int), Seq[(Expr,Expr)]].withDefaultValue(Seq())

    /* Gives the index of f in chain c. */
    def domIndex(rs: Seq[Relation], f: FunDef, i: Int): Int = rs match {
      case Relation(fd,_,fi,_) :: _ if (fd.id == f.id) => i
      case Relation(fd,_,fi,_) :: _ if (fi.id == f.id) => i+1
      case r :: rs => domIndex(rs,f,i+1)
      case _ => -1
    }

    val M = cs.map{ c => c.size }.max

    def measure(expr: Seq[Expr]) =
      ordering.measure(Seq(recons(tupleWrap(expr))))
    def tupleMeasure(expr: Expr, j: Int, k: Int) =
      tupleWrap(Seq(expr, IntegerLiteral(j), IntegerLiteral(k)))

    /* Annotate the base of a sequence of chains. */
    def annotateBase(base: FunDef, cs: Seq[Chain]) = {
      val args = measure(base.params.map(_.toVariable))
      val baseCond =
        orJoin(cs.map{ c => Chain(c.relations).loop._1.toClause })
      val baseMeasure = tupleMeasure(args,0,0)
      annotationMap += ((base,-1) -> (annotationMap((base,-1)) :+ (baseCond,baseMeasure)))
    }

    def annotateLoops(base: FunDef, cs: Seq[Chain]) = {
      // I assume the chains cs start at base
      for (c <- cs; member <- c.fds if member.id != base.id) {
        val i = domIndex(c.relations,member,0)
        val domRelations = c.relations.drop(i)

        // annotate looping condition
        val (domRpath,args1) = Chain(domRelations).loop
        val margs1 = bindingsToLets(domRpath.bindings, measure(args1))
        val cond1 = domRpath.toClause
        val measure1 = tupleMeasure(margs1,M-i,M)
        annotationMap += ((member,-1) -> (annotationMap((member,-1)) :+ (cond1,measure1)))

        // annotate escaping steps
        var relations = domRelations.dropRight(1)
        while(!relations.isEmpty){
          val (path,_) = Chain(relations).loop
          val steps = relations.size
          val cond2 = path.toClause
          val measure2 = tupleMeasure(IntegerLiteral(0),0,M-(steps))
          annotationMap += ((member,steps) -> (annotationMap((member,steps)) :+ (cond2,measure2)))
          relations = relations.dropRight(1)
        }

        val noCond = not(cond1)
        val noMeasure = tupleMeasure(IntegerLiteral(0),0,M-i)
        annotationMap += ((member,0) -> (annotationMap((member,0)) :+ (noCond,noMeasure)))
      }
    }

    def buildMeasure(): Unit = {
      val default = tupleMeasure(IntegerLiteral(0),0,M)

      /* Annotation map with format: f -> (index -> Seq(values)) */
      val indexedByFun =
        annotationMap.groupBy(_._1._1)
          .view.mapValues(_.map{ case (k,v) => k._2 -> v })
          .toMap

      for((k,v) <- indexedByFun.toSeq) yield {
        val orderedMeasures: List[(Int, Seq[(Expr,Expr)])] = v.toList.sortBy(_._1)
        /* Measures has -1 at the end and flattened */
        val measures: List[(Int, Seq[(Expr,Expr)])]  =
          if(orderedMeasures.head._1 == -1){
            orderedMeasures.tail ++ orderedMeasures.head._2.map(m => -1 -> Seq(m)).toList
          } else {
            orderedMeasures.tail
          }

        val measure = measures.foldLeft(default){ case (acc,(_, seq)) =>
          if(!seq.isEmpty){
            val expr = seq.head._2
            IfExpr(orJoin(seq.map(_._1)),expr,acc)
          } else {
            acc
          }
        }

        measureCache += k -> measure
      }
    }

    annotateBase(base, cs)
    annotateLoops(base,cs)
    buildMeasure()
   }
}

