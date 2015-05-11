/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._
import purescala.Expressions._

import scala.collection.mutable.{Map => MutableMap}

class ComplexTerminationChecker(context: LeonContext, program: Program)
       extends ProcessingPipeline(context, program)
          with StructuralSize
          with RelationComparator
          with ChainComparator
          with Strengthener
          with RelationBuilder
          with ChainBuilder {

  val name = "Complex Termination Checker"
  val description = "A modular termination checker with a few basic modules™"

  def processors = List(
    new RecursionProcessor(this),
    new RelationProcessor(this),
    new ChainProcessor(this),
    new LoopProcessor(this)
  )

}
