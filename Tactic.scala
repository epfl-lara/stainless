package leon
package verification

import Extensions.Extension

import purescala.Definitions._

abstract class Tactic(reporter: Reporter) extends Extension(reporter) {
  def setProgram(program: Program) : Unit = {}
  def generatePostconditions(function: FunDef) : Seq[VerificationCondition]
  def generatePreconditions(function: FunDef) : Seq[VerificationCondition]
  def generatePatternMatchingExhaustivenessChecks(function: FunDef) : Seq[VerificationCondition]
  def generateMiscCorrectnessConditions(function: FunDef) : Seq[VerificationCondition]
  def generateArrayAccessChecks(function: FunDef) : Seq[VerificationCondition]
}
