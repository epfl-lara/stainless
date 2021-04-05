/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, HashSet => MutableSet, ListBuffer => MutableList}

trait MeasureInference
  extends extraction.CachingPhase
    with extraction.SimplyCachedSorts
    with extraction.IdentitySorts
    with extraction.SimpleFunctions { self =>

  val s: Trees
  val t: Trees
  import s._

  import context.{options, timers, reporter}

  // Measure inference depends on functions that are mutually recursive with `fd`,
  // so we include all dependencies in the key calculation
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) =>
    getDependencyKey(fd.id)(context.symbols)
  )

  val sizes: SizeFunctions { val trees: s.type } = new {
    val trees: s.type = self.s
  } with SizeFunctions

  type Postconditions  = MutableMap[Identifier, Option[Lambda]]
  type Applications    = MutableMap[(Identifier, Identifier, Identifier), Expr]

  override protected def getContext(symbols: s.Symbols) = TransformerContext(symbols, MutableMap.empty, MutableMap.empty)

  protected case class TransformerContext(symbols: Symbols, 
                                          measureCache: MutableMap[FunDef, Expr], 
                                          annotationMap: MutableMap[FunDef, (Postconditions, Applications)]) {
    val program = inox.Program(s)(symbols)

    val pipeline = TerminationChecker(program, self.context)(sizes)

    final object transformer extends inox.transformers.TreeTransformer {
      override val s: self.s.type = self.s
      override val t: self.t.type = self.t

      override def transform(e: s.Expr): t.Expr = e match {
        case Decreases(v: Variable, body) if v.getType(symbols).isInstanceOf[ADTType] =>
          t.Decreases(transform(size(v)), transform(body)).setPos(e)

        case Decreases(Tuple(ts), body) =>
          t.Decreases(t.Tuple(ts.map {
            case v: Variable if v.getType(symbols).isInstanceOf[ADTType] => transform(size(v))
            case e => transform(e)
          }), transform(body)).setPos(e)

        case _ =>
          super.transform(e)
      }

      private def size(v: Variable): Expr = {
        require(v.getType(symbols).isInstanceOf[ADTType])
        val ADTType(id, tps) = v.getType(symbols)
        FunctionInvocation(sizes.fullSizeId(symbols.sorts(id)), tps, Seq(v)).setPos(v)
      }
    }

    def needsMeasure(fd: FunDef): Boolean =
      symbols.isRecursive(fd.id) && fd.measure(symbols).isEmpty

    def annotatePosts(original: FunDef, posts: Postconditions) = posts.get(original.id) match {
      case Some(post) => original.copy(fullBody = exprOps.withPostcondition(original.fullBody, post))
      case None       => original
    }      

    def annotateApps(original: FunDef, apps: Applications) = {
      object injector extends inox.transformers.TreeTransformer {
        val s: self.s.type = self.s
        val t: self.s.type = self.s

        override def transform(e: Expr): Expr = e match {
          case fi @ FunctionInvocation(_, _, args) =>
            fi.copy(args = (symbols.getFunction(fi.id).params.map(_.id) zip args).map {
              case (id, l @ Lambda(largs, body)) if apps.isDefinedAt(original.id, fi.id,id) =>
                val cnstr = apps(original.id, fi.id,id)
                reporter.info(original.getPos, s"Adding assume ${cnstr}")
                println("adding assume " + Lambda(largs, Assume(cnstr, body)))
                Lambda(largs, Assume(cnstr, body))
              case (_, arg) => transform(arg)
            })            
          case _ =>
            super.transform(e)
        }
      }

      injector.transform(original)
    }

    def annotate(original: FunDef) = annotationMap.get(original) match {
      case Some((posts, apps)) => 
        val fid = symbols.getFunction(original.id)
        // annotate posts and apps
        annotateApps(annotatePosts(original, posts),apps)
      case None                => 
        reporter.warning(original.getPos, s"No annotations found for function ${original.id.asString}")
        original
    }

    def inferMeasure(original: FunDef): FunDef = measureCache.get(original) match {
      case Some(measure) =>
        val annotated = annotate(original)
        println("annotated")
        println(annotated)
        annotated.copy(fullBody = exprOps.withMeasure(annotated.fullBody, Some(measure.setPos(original))))

      case None => try {
        val guarantee = timers.evaluators.termination.inference.run {
          reporter.info(s"  - Inferring measure for ${original.id.asString}...")
          pipeline.terminates(original)
        }

        val result = guarantee match {
          case pipeline.Terminates(_, Some(measure), Some(lemmas)) =>
            reporter.info(s" => Found measure for ${original.id.asString}.")
            measureCache ++= pipeline.measureCache.get
            annotationMap += original -> lemmas
            val annotated = annotate(original)
            println("annotated")
            println(annotated)
            annotated.copy(fullBody = exprOps.withMeasure(annotated.fullBody, Some(measure.setPos(original))))

          case pipeline.Terminates(_, None, _) =>
            reporter.info(s" => No measure needed for ${original.id.asString}.")
            original

          case _ if exprOps.measureOf(original.fullBody).isDefined =>
            reporter.info(s" => Function ${original.id.asString} already has a measure.")
            original

          case nt: pipeline.NonTerminating =>
            reporter.warning(original.getPos, nt.asString)
            original

          case _ =>
            reporter.warning(original.getPos, s"Could not infer measure for function ${original.id.asString}")
            original
        }

        annotate(result, guarantee)
      } catch {
        case FailedMeasureInference(fd, msg) =>
          reporter.warning(fd.getPos, msg)
          original
      }
    }

    private def annotate(fd: FunDef, guarantee: pipeline.TerminationGuarantee): FunDef = {
      fd.copy(flags = fd.flags :+ TerminationStatus(status(guarantee)))
    }

    private def status(g: pipeline.TerminationGuarantee): TerminationReport.Status = g match {
      case pipeline.NoGuarantee       => TerminationReport.Unknown
      case pipeline.Terminates(_,_,_) => TerminationReport.Terminating
      case _                          => TerminationReport.NonTerminating
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    if (options.findOptionOrDefault(optInferMeasures) && context.needsMeasure(fd)) {
      val res = context.inferMeasure(fd)
      println("res")
      println(res)
      val res2 = context.transformer.transform(res)
      println("res2")
      println(res2)
      res2
    } else {
      context.transformer.transform(fd)
    }
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val extracted = super.extractSymbols(context, symbols)
    val sizeFunctions = sizes.getFunctions(symbols).map(context.transformer.transform(_))
    registerFunctions(extracted, sizeFunctions)
  }
}

object MeasureInference { self =>
  def apply(tr: Trees)(implicit ctx: inox.Context): extraction.ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = new {
    override val s: tr.type = tr
    override val t: tr.type = tr
    override val context = ctx
  } with MeasureInference
}
