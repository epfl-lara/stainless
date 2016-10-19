/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.duration._

object DebugSectionTermination extends inox.DebugSection("termination")

trait TerminationChecker {
  val program: Program
  import program.trees._

  def terminates(fd: FunDef): TerminationGuarantee

  sealed abstract class TerminationGuarantee {
    def isGuaranteed: Boolean
  }

  case class Terminates(reason: String) extends TerminationGuarantee {
    override def isGuaranteed: Boolean = true
  }

  abstract class NonTerminating extends TerminationGuarantee {
    override def isGuaranteed: Boolean = false
  }

  case class LoopsGivenInputs(reason: String, args: Seq[Expr]) extends NonTerminating
  case class MaybeLoopsGivenInputs(reason: String, args: Seq[Expr]) extends NonTerminating

  case class CallsNonTerminating(calls: Set[FunDef]) extends NonTerminating

  case object NoGuarantee extends TerminationGuarantee {
    override def isGuaranteed: Boolean = false
  }
}

object TerminationChecker {
  def apply(p: StainlessProgram): TerminationChecker { val program: p.type } = new ProcessingPipeline { self =>
    val program: p.type = p
    import p.trees._

    def getSolver(transformer: inox.ast.SymbolTransformer { val transformer: SelfTransformer }) =
      solvers.SolverFactory.default(p).withTimeout(1.seconds)

    object integerOrdering extends {
      val checker: self.type = self
    } with SumOrdering
      with StructuralSize
      with Strengthener
      with RelationBuilder
      with ChainBuilder

    object lexicographicOrdering extends {
      val checker: self.type = self
    } with LexicographicOrdering
      with StructuralSize
      with Strengthener
      with RelationBuilder

    object bvOrdering extends {
      val checker: self.type = self
    } with BVOrdering
      with StructuralSize
      with Strengthener
      with RelationBuilder

    object recursionProcessor extends {
      val checker: self.type = self
      val builder: integerOrdering.type = integerOrdering
    } with RecursionProcessor

    object selfCallsProcessor extends {
      val checker: self.type = self
    } with SelfCallsProcessor

    object integerProcessor extends {
      val checker: self.type = self
      val ordering: integerOrdering.type = integerOrdering
    } with RelationProcessor

    object lexicographicProcessor extends {
      val checker: self.type = self
      val ordering: lexicographicOrdering.type = lexicographicOrdering
    } with RelationProcessor

    object bvProcessor extends {
      val checker: self.type = self
      val ordering: bvOrdering.type = bvOrdering
    } with RelationProcessor

    object chainProcessor extends {
      val checker: self.type = self
      val ordering: integerOrdering.type = integerOrdering
    } with ChainProcessor

    object loopProcessor extends {
      val checker: self.type = self
      val ordering: integerOrdering.type = integerOrdering
    } with LoopProcessor

    val processors = List(
      recursionProcessor,
      selfCallsProcessor,
      integerProcessor,
      lexicographicProcessor,
      bvProcessor,
      chainProcessor,
      loopProcessor
    )
  }
}
