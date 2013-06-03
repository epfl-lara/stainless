/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._

abstract class TerminationChecker(val context : LeonContext, val program : Program) extends LeonComponent {
  
  def terminates(funDef : FunDef) : TerminationGuarantee
}

sealed abstract class TerminationGuarantee {
  val isGuaranteed : Boolean = false
}

case class TerminatesForAllInputs(justification : String) extends TerminationGuarantee {
  override val isGuaranteed : Boolean = true
}
case object NoGuarantee extends TerminationGuarantee
