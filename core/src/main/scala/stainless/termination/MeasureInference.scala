/* Copyright 2009-2019 EPFL, Lausanne */

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

  override protected def getContext(symbols: s.Symbols) = TransformerContext(symbols, MutableMap.empty)

  protected case class TransformerContext(symbols: Symbols, measureCache: MutableMap[FunDef, Expr]) {
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

    def inferMeasure(original: FunDef): FunDef = measureCache.get(original) match {
      case Some(measure) =>
        original.copy(fullBody = exprOps.withMeasure(original.fullBody, Some(measure.setPos(original))))

      case None => try {
        val guarantee = timers.evaluators.termination.inference.run {
          reporter.info(s"  - Inferring measure for ${original.id.asString}...")
          pipeline.terminates(original)
        }

        val result = guarantee match {
          case pipeline.Terminates(_, Some(measure)) =>
            reporter.info(s" => Found measure for ${original.id.asString}.")
            measureCache ++= pipeline.measureCache.get
            original.copy(fullBody = exprOps.withMeasure(original.fullBody, Some(measure.setPos(original))))

          case pipeline.Terminates(_, None) =>
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
      case pipeline.NoGuarantee      => TerminationReport.Unknown
      case pipeline.Terminates(_, _) => TerminationReport.Terminating
      case _                         => TerminationReport.NonTerminating
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    if (options.findOptionOrDefault(optInferMeasures) && context.needsMeasure(fd)) {
      context.transformer.transform(context.inferMeasure(fd))
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
