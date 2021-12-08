/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, ListBuffer => MutableList}

trait TerminationChecker { self =>
  val program: Program { val trees: Trees }
  val context: inox.Context

  import program.trees._
  import program.symbols.{given, _}

  def terminates(fd: FunDef): TerminationGuarantee

  /* Caches for inductive lemmas */
  type Postconditions  = MutableMap[Identifier, Lambda]
  type Applications    = MutableMap[(Identifier, Identifier, Identifier), Seq[ValDef] => Expr]
  type InductiveLemmas = Option[(Postconditions, Applications)]
  /* End caches for inductive lemmas */

  sealed abstract class TerminationGuarantee {
    def isGuaranteed: Boolean
  }

  case class Terminates(reason: String, measure: Option[Expr], lemmas: InductiveLemmas) extends TerminationGuarantee {
    override def isGuaranteed: Boolean = true
  }

  sealed abstract class NonTerminating extends TerminationGuarantee {
    override def isGuaranteed: Boolean = false

    def asString(using PrinterOptions): String = this match {
      case NotWellFormed(sorts) =>
        s"ADTs ${sorts.map(_.id.asString).mkString(", ")} are ill-formed"
      case LoopsGivenInputs(fi) =>
        if (fi.args.nonEmpty) {
          val max = fi.tfd.params.map(_.asString.length).max
          val model = for ((vd, e) <- fi.tfd.params zip fi.args) yield {
            ("%-" + max + "s -> %s").format(vd.asString, e.asString)
          }
          s"Function ${fi.id.asString} loops given inputs:\n${model.mkString("\n")}"
        } else {
          s"Function ${fi.id.asString} loops when called"
        }
      case MaybeLoopsGivenInputs(fi) =>
        if (fi.args.nonEmpty) {
          val max = fi.tfd.params.map(_.asString.length).max
          val model = for ((vd, e) <- fi.tfd.params zip fi.args) yield {
            ("%-" + max + "s -> %s").format(vd.asString, e.asString)
          }
          s"Function ${fi.id.asString} maybe loops given inputs:\n${model.mkString("\n")}"
        } else {
          s"Function ${fi.id.asString} maybe loops when called"
        }
      case CallsNonTerminating(calls) =>
        s"Calls non-terminating functions ${calls.map(_.id.asString).mkString(", ")}"
      case DecreasesFailed(fd) =>
        s"Decreases check failed for ${fd.id.asString}"
    }
  }

  case class NotWellFormed(sorts: Set[ADTSort]) extends NonTerminating
  case class LoopsGivenInputs(fi: FunctionInvocation) extends NonTerminating
  case class MaybeLoopsGivenInputs(fi: FunctionInvocation) extends NonTerminating
  case class CallsNonTerminating(calls: Set[FunDef]) extends NonTerminating
  case class DecreasesFailed(fd: FunDef) extends NonTerminating

  case object NoGuarantee extends TerminationGuarantee {
    override def isGuaranteed: Boolean = false
  }

  object measureCache {
    private val cache: MutableMap[FunDef, Expr] = MutableMap.empty

    def add(p: (FunDef, Expr)) = cache += p
    def get = cache
  }

  val integerOrdering: StructuralSize with SolverProvider {
    val checker: self.type
  }

  val lexicographicOrdering: StructuralSize with SolverProvider {
    val checker: self.type
  }

  val bvOrdering: StructuralSize with SolverProvider {
    val checker: self.type
  }

  def get = {
    integerOrdering.functions ++
    lexicographicOrdering.functions ++
    bvOrdering.functions
  }
}

object TerminationChecker {

  def apply(p: Program { val trees: Trees }, ctx: inox.Context)(sze: SizeFunctions { val trees: p.trees.type })
      : TerminationChecker { val program: p.type } = {

    class EncoderImpl(override val s: p.trees.type, override val t: stainless.trees.type)
      extends inox.transformers.TreeTransformer {
      override def transform(e: s.Expr): t.Expr = e match {
        case s.Decreases(measure, body) => transform(body)
        case _                          => super.transform(e)
      }
    }

    val encoderImpl = new EncoderImpl(p.trees, stainless.trees)

    class ProcessingPipelineImpl(override val program: p.type, override val context: inox.Context) extends ProcessingPipeline {
      self =>

      class CFAImpl(override val program: self.program.type)
        extends CICFA(program, self.context)
      val cfa = new CFAImpl(self.program)

      class IntegerOrderingImpl(override val checker: self.type, override val sizes: sze.type,
                                override val cfa: self.cfa.type, override val encoder: encoderImpl.type)
        extends SumOrdering with StructuralSize with Strengthener with RelationBuilder with ChainBuilder
      // We explicitly widen integerOrdering because scalac seems to ignore some of the mixed traits if we don't do so.
      val integerOrdering: SumOrdering with StructuralSize with Strengthener with RelationBuilder with ChainBuilder {
        val checker: self.type
      } = new IntegerOrderingImpl(self, sze, self.cfa, encoderImpl)

      class LexicographicOrderingImpl(override val checker: self.type, override val sizes: sze.type,
                                      override val cfa: self.cfa.type, override val encoder: encoderImpl.type)
        extends LexicographicOrdering with StructuralSize with Strengthener with RelationBuilder
      // Ditto
      val lexicographicOrdering: LexicographicOrdering with StructuralSize with Strengthener with RelationBuilder {
        val checker: self.type
      } = new LexicographicOrderingImpl(self, sze, self.cfa, encoderImpl)

      class BVOrderingImpl(override val checker: self.type, override val sizes: sze.type,
                           override val cfa: self.cfa.type, override val encoder: encoderImpl.type)
        extends BVOrdering with StructuralSize with Strengthener with RelationBuilder
      // Ditto
      val bvOrdering: BVOrdering with StructuralSize with Strengthener with RelationBuilder {
        val checker: self.type
      } = new BVOrderingImpl(self, sze, self.cfa, encoderImpl)

      class RecursionProcessorImpl(override val checker: self.type,
                                   override val ordering: integerOrdering.type)
        extends RecursionProcessor(checker, ordering)
      val recursionProcessor = new RecursionProcessorImpl(self, integerOrdering)

      class DecreasesProcessorImpl(override val checker: self.type, override val ordering: integerOrdering.type)
        extends DecreasesProcessor(checker, ordering)
      val decreasesProcessor = new DecreasesProcessorImpl(self, integerOrdering)

      class SelfCallsProcessorImpl(override val checker: self.type)
        extends SelfCallsProcessor(checker)
      val selfCallsProcessor = new SelfCallsProcessorImpl(self)

      class IntegerProcessorImpl(override val checker: self.type, override val ordering: integerOrdering.type)
        extends RelationProcessor(checker, ordering)
      val integerProcessor = new IntegerProcessorImpl(self, integerOrdering)

      class LexicographicProcessorImpl(override val checker: self.type, override val ordering: lexicographicOrdering.type)
        extends RelationProcessor(checker, ordering)
      val lexicographicProcessor = new LexicographicProcessorImpl(self, lexicographicOrdering)

      class BVProcessorImpl(override val checker: self.type, override val ordering: bvOrdering.type)
        extends RelationProcessor(checker, ordering)
      val bvProcessor = new BVProcessorImpl(self, bvOrdering)

      class ChainProcessorImpl(override val checker: self.type, override val ordering: integerOrdering.type)
        extends ChainProcessor(checker, ordering)
      val chainProcessor = new ChainProcessorImpl(self, integerOrdering)

      class LoopProcessorImpl(override val checker: self.type, override val ordering: integerOrdering.type)
        extends LoopProcessor(checker, ordering)
      val loopProcessor = new LoopProcessorImpl(self, integerOrdering)

      val processors = {
        List(
          recursionProcessor,
          selfCallsProcessor,
          decreasesProcessor,
          integerProcessor,
          lexicographicProcessor,
          bvProcessor,
          chainProcessor,
          loopProcessor,
        )
      }
    }
    new ProcessingPipelineImpl(p, ctx)
  }
}
