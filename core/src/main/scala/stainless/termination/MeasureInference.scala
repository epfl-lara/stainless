/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, HashSet => MutableSet, ListBuffer => MutableList}

object DebugSectionMeasureInference extends inox.DebugSection("measure-inference")

class MeasureInference(override val s: Trees, override val t: Trees)(using override val context: inox.Context)
  extends extraction.CachingPhase
     with extraction.SimplyCachedSorts
     with extraction.IdentitySorts { self =>

  import s._

  import context.{options, timers, reporter}

  type Postconditions  = MutableMap[Identifier, Lambda]
  type Applications    = MutableMap[(Identifier, Identifier, Identifier), Seq[ValDef] => Expr]
  // Result type is transformed function + all inductive lemmas found
  type FunctionResult = (t.FunDef, Postconditions)

  given givenDebugSection: DebugSectionMeasureInference.type = DebugSectionMeasureInference

  // Measure inference depends on functions that are mutually recursive with `fd`,
  // so we include all dependencies in the key calculation
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  val sizes: SizeFunctions { val trees: s.type } = {
    class SizeFunctionsImpl(override val trees: s.type) extends SizeFunctions(trees)
    new SizeFunctionsImpl(s)
  }

  override protected def getContext(symbols: s.Symbols) = TransformerContext(symbols, MutableMap.empty, MutableMap.empty, MutableMap.empty)

  protected case class TransformerContext(symbols: Symbols,
                                          measureCache:       MutableMap[FunDef, Expr],
                                          postconditionCache: MutableMap[Identifier, Postconditions],
                                          applicationCache:   Applications) {
    import symbols.given
    val program = inox.Program(s)(symbols)

    val pipeline = TerminationChecker(program, self.context)(sizes)

    val transformer = new TransformerImpl(self.s, self.t)

    class TransformerImpl(override val s: self.s.type, override val t: self.t.type)
      extends inox.transformers.ConcreteTreeTransformer(s, t) {

      override def transform(e: s.Expr): t.Expr = e match {
        case Decreases(v: Variable, body) if v.getType.isInstanceOf[ADTType] =>
          t.Decreases(transform(size(v)), transform(body)).setPos(e)

        case Decreases(tup @ Tuple(ts), body) =>
          t.Decreases(t.Tuple(ts.map {
            case v: Variable if v.getType.isInstanceOf[ADTType] => transform(size(v))
            case e => transform(e)
          }).copiedFrom(tup), transform(body)).setPos(e)

        case _ =>
          super.transform(e)
      }

      private def size(v: Variable): Expr = {
        require(v.getType.isInstanceOf[ADTType])
        val ADTType(id, tps) = v.getType
        FunctionInvocation(sizes.fullSizeId(symbols.sorts(id)), tps, Seq(v)).setPos(v)
      }
    }

    def needsMeasure(fd: FunDef): Boolean = symbols.isRecursive(fd.id) && {
      val specced = exprOps.BodyWithSpecs(fd.fullBody)
      !specced.specs.exists(_.kind == exprOps.MeasureKind)
    }

    def getPosts(id: Identifier): Postconditions =
      postconditionCache.getOrElse(id, MutableMap())

    def annotateApps(original: FunDef) = {
      class Injector(override val s: self.s.type, override val t: self.s.type)
        extends inox.transformers.ConcreteTreeTransformer(s, t) {
        override def transform(e: Expr): Expr = e match {
          case fi @ FunctionInvocation(_, _, args) =>
            fi.copy(args = (symbols.getFunction(fi.id).params.map(_.id) zip args).map {
              case (id, l @ Lambda(largs, body)) if applicationCache.isDefinedAt(original.id, fi.id,id) =>
                val cnstr = applicationCache(original.id, fi.id,id)
                body match {
                  case FunctionInvocation(lid,_,_) if lid == original.id =>
                    Lambda(largs, Assume(cnstr(largs), body))
                  case _                         =>
                    /*
                      a) This avoids a problem detected in LawTypeArgsElim.scala.
                      Annotating assume makes appear an undeclared variable in the
                      assumption and type checking fails.

                      b) This avoids annotating the lambda when it is not needed for
                      termination (condition lid == original.id). Annotating in that
                      case may make it difficult for the SMT solvers in some instances.
                    */
                    l
                }

              case (_, arg) => transform(arg)
            }).copiedFrom(fi)
          case _ =>
            super.transform(e)
        }
      }

      new Injector(self.s, self.s).transform(original)
    }

    /* Annotation order matters, postconditions can
       introduce size functions which are yet unknown
       in the symbols */
    def annotate(original: FunDef) = annotateApps(original)

    def inferMeasure(original: FunDef): FunDef = measureCache.get(original) match {
      case Some(measure) =>
        val annotated = annotate(original)
        annotated.copy(fullBody = exprOps.withMeasure(annotated.fullBody, Some(measure.setPos(original))))

      case None => try {
        val guarantee = timers.evaluators.termination.inference.run {
          reporter.debug(s"  - Inferring measure for ${original.id.asString}...")
          pipeline.terminates(original)
        }

        val result = guarantee match {
          case pipeline.Terminates(_, Some(measure), Some(lemmas)) =>
            reporter.debug(s" => Found measure for ${original.id.asString}.")
            measureCache ++= pipeline.measureCache.get
            pipeline.measureCache.get.keys.map{ fd =>
              postconditionCache(fd.id) = lemmas._1
            }
            applicationCache ++= lemmas._2
            val annotated = annotate(original)
            annotated.copy(fullBody = exprOps.withMeasure(annotated.fullBody, Some(measure.setPos(original))))
                     .setPos(original)

          case pipeline.Terminates(_, None, _) =>
            reporter.debug(s" => No measure needed for ${original.id.asString}.")
            original

          case _ if exprOps.measureOf(original.fullBody).isDefined =>
            reporter.debug(s" => Function ${original.id.asString} already has a measure.")
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
      fd.copy(flags = fd.flags :+ TerminationStatus(status(guarantee))).copiedFrom(fd)
    }

    private def status(g: pipeline.TerminationGuarantee): TerminationReport.Status = g match {
      case pipeline.NoGuarantee       => TerminationReport.Unknown
      case pipeline.Terminates(_,_,_) => TerminationReport.Terminating
      case _                          => TerminationReport.NonTerminating
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): FunctionResult = {
    if (options.findOptionOrDefault(optInferMeasures) && context.needsMeasure(fd)) {
      val tfd   = context.transformer.transform(context.inferMeasure(fd))
      val posts = context.getPosts(fd.id)
      (tfd, posts)
    } else {
      (context.transformer.transform(fd), MutableMap.empty)
    }
  }

  override def registerFunctions(symbols: t.Symbols, functions: Seq[FunctionResult]): t.Symbols =
    symbols

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val results: Seq[(t.FunDef, MutableMap[Identifier,s.Lambda])] =
      symbols.functions.values.map(fd =>
        funCache.cached(fd, context)(extractFunction(context,fd))
      ).toSeq

    val posts: Map[Identifier, s.Lambda] = results.flatMap{ case (tfd,post) => post }.toMap

    def annotatePosts(original: t.FunDef) = {
      class PostTransformer(override val s: self.s.type, override val t: self.t.type)
        extends transformers.ConcreteTreeTransformer(s, t)
      val postTransformer = new PostTransformer(self.s, self.t)

      val postCache: Map[Identifier, t.Lambda] =
        posts.view.mapValues{ (v: s.Lambda) =>
          postTransformer.transform(v).asInstanceOf[t.Lambda]
        }.toMap
      postCache.get(original.id) match {
        case Some(post@t.Lambda(Seq(nlarg), nbody)) =>
          val newVd = t.ValDef.fresh("arg", original.returnType)
          val newMap: Map[t.ValDef, t.Expr] = Map((nlarg, newVd.toVariable))
          val newNBody: t.Expr = t.exprOps.replaceFromSymbols(newMap, nbody)(using t.convertToVal)
          val refinement = t.RefinementType(newVd, newNBody)
          original.copy(returnType = refinement).copiedFrom(original)
        case None       => original
      }
    }

    val sizeFunctions: Seq[t.FunDef] =
      sizes.getFunctions(symbols).map(context.transformer.transform(_)).toSeq

    val functions = results.map { case (tfd, post) =>
      annotatePosts(tfd)
    }.toSeq

    val sorts = symbols.sorts.values.map { sort =>
      sortCache.cached(sort, context)(extractSort(context, sort))
    }.toSeq

    t.NoSymbols.withSorts(sorts).withFunctions(functions ++ sizeFunctions)
  }
}

object MeasureInference { self =>
  def apply(tr: Trees)(using inox.Context): extraction.ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = {
    class Impl(override val s: tr.type, override val t: tr.type) extends MeasureInference(s, t)
    new Impl(tr, tr)
  }
}
