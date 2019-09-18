/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

object DebugSectionTermination extends inox.DebugSection("termination")

trait TerminationChecker {
  val program: Program { val trees: ast.Trees }
  val context: inox.Context
  import program.trees._
  import program.symbols._

  def terminates(fd: FunDef): TerminationGuarantee

  sealed abstract class TerminationGuarantee {
    def isGuaranteed: Boolean
  }

  case class Terminates(reason: String) extends TerminationGuarantee {
    override def isGuaranteed: Boolean = true
  }

  sealed abstract class NonTerminating extends TerminationGuarantee {
    override def isGuaranteed: Boolean = false
    def asString(implicit opts: PrinterOptions): String = this match {
      case NotWellFormed(sorts) =>
        s"Adts ${sorts.map(_.id.asString).mkString(", ")} are ill-formed"
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
}

object TerminationChecker {
  def apply(p: TerminationProgram, ctx: inox.Context): TerminationChecker { val program: p.type } = new {
    val program: p.type = p
    val context = ctx
  } with ProcessingPipeline { self =>
    import p.trees._

    object encoder extends {
      val s: p.trees.type = p.trees
      val t: stainless.trees.type = stainless.trees
    } with transformers.TreeTransformer {
      override def transform(e: s.Expr): t.Expr = e match {
        case s.Decreases(measure, body) => transform(body)
        case _ => super.transform(e)
      }
    }

    object cfa extends CICFA {
      val program: self.program.type = self.program
      val context = self.context
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
