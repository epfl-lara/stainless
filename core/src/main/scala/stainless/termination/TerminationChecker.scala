/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

object DebugSectionTermination extends inox.DebugSection("termination")

trait TerminationChecker {
  val program: Program { val trees: Trees }
  val options: inox.Options
  import program.trees._

  def terminates(fd: FunDef): TerminationGuarantee

  sealed abstract class TerminationGuarantee {
    def isGuaranteed: Boolean
  }

  case class Terminates(reason: String) extends TerminationGuarantee {
    override def isGuaranteed: Boolean = true
  }

  sealed abstract class NonTerminating extends TerminationGuarantee {
    override def isGuaranteed: Boolean = false
  }

  case class LoopsGivenInputs(reason: String, args: Seq[Expr]) extends NonTerminating
  case class MaybeLoopsGivenInputs(reason: String, args: Seq[Expr]) extends NonTerminating
  case class CallsNonTerminating(calls: Set[FunDef]) extends NonTerminating
  case object DecreasesFailed extends NonTerminating

  case object NoGuarantee extends TerminationGuarantee {
    override def isGuaranteed: Boolean = false
  }
}

object TerminationChecker {
  def apply(p: TerminationProgram, opts: inox.Options): TerminationChecker { val program: p.type } = new {
    val program: p.type = p
    val options = opts
  } with ProcessingPipeline { self =>
    import p.trees._

    object encoder extends {
      val s: p.trees.type = p.trees
      val t: stainless.trees.type = stainless.trees
    } with ast.TreeTransformer {
      override def transform(e: s.Expr): t.Expr = e match {
        case s.Decreases(measure, body) => transform(body)
        case _ => super.transform(e)
      }
    }

    object cfa extends CICFA {
      val program: self.program.type = self.program
    }

    object integerOrdering extends {
      val checker: self.type = self
      val cfa: self.cfa.type = self.cfa
      val encoder: self.encoder.type = self.encoder
    } with SumOrdering
      with StructuralSize
      with Strengthener
      with RelationBuilder
      with ChainBuilder

    object lexicographicOrdering extends {
      val checker: self.type = self
      val cfa: self.cfa.type = self.cfa
      val encoder: self.encoder.type = self.encoder
    } with LexicographicOrdering
      with StructuralSize
      with Strengthener
      with RelationBuilder

    object bvOrdering extends {
      val checker: self.type = self
      val cfa: self.cfa.type = self.cfa
      val encoder: self.encoder.type = self.encoder
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

    object decreasesProcessor extends {
      val checker: self.type = self
      val ordering: integerOrdering.type = integerOrdering
    } with DecreasesProcessor

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
      decreasesProcessor,
      integerProcessor,
      lexicographicProcessor,
      bvProcessor,
      chainProcessor,
      loopProcessor
    )
  }
}
