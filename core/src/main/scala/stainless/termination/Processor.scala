/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

trait Processor {
  val name: String

  val checker: ProcessingPipeline

  implicit val debugSection = DebugSectionTermination

  def run(problem: checker.Problem): Option[Seq[checker.Result]]
}

trait OrderingProcessor extends Processor {

  val ordering: OrderingRelation with Strengthener {
    val checker: OrderingProcessor.this.checker.type
  }
}

