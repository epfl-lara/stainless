/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._
import purescala.Expressions._

import scala.collection.mutable.{Map => MutableMap}

class ComplexTerminationChecker(context: LeonContext, program: Program) extends ProcessingPipeline(context, program) {

  val name = "Complex Termination Checker"
  val description = "A modular termination checker with a few basic modules™"

  val modules =
        new StructuralSize
       with ArgsSizeSumRelationComparator
       with ChainComparator
       with Strengthener
       with RelationBuilder
       with ChainBuilder 
  {
    val checker = ComplexTerminationChecker.this
  }

  val modulesLexicographic =
        new StructuralSize
       with LexicographicRelationComparator
       with ChainComparator
       with Strengthener
       with RelationBuilder
       with ChainBuilder 
  {
    val checker = ComplexTerminationChecker.this
  }

  def processors = List(
    new RecursionProcessor(this, modules),
    // RelationProcessor is the only Processor which benefits from trying a different RelationComparator
    new RelationProcessor(this, modules),
    new RelationProcessor(this, modulesLexicographic),
    new ChainProcessor(this, modules),
    new SelfCallsProcessor(this),
    new LoopProcessor(this, modules)
  )

}
