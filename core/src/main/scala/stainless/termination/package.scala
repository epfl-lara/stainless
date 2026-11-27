/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import stainless.utils.YesNoOnly

package object termination {

  type Trees = extraction.Trees
  val trees = extraction.trees

  object optInferMeasures extends inox.FlagOptionDef("infer-measures", true)

  object optCheckMeasures extends inox.OptionDef[YesNoOnly] {
    val name     = "check-measures"
    val default  = YesNoOnly.Yes
    val parser   = YesNoOnly.parse(_)
    val usageRhs = "yes | no | only"
  }

  /** How much work the termination checker's queries may each do when the solvers have a resource
    * limit (`--z3-rlimit`, `--cvc5-rlimit`), as a factor of [[TerminationWork.baseRlimit]] millions of
    * resource units per check and of [[TerminationWork.baseUnrollBound]] unrollings, see [[SolverProvider]]. */
  object optTerminationWork extends inox.DoubleOptionDef("termination-work", 1.0, "<PosDouble>")

  object TerminationWork {
    val baseRlimit: Int = 5
    val baseUnrollBound: Int = 16

    private def scaled(base: Int, work: Double): Int = (base * work).round.toInt max 1

    /** The resource limit of each check, in millions of units, for the given work factor. */
    def rlimit(work: Double): Int = scaled(baseRlimit, work)

    /** The unrolling bound of each query for the given work factor. */
    def unrollBound(work: Double): Int = scaled(baseUnrollBound, work)
  }

  object DebugSectionTermination extends inox.DebugSection("termination")

  case class FailedMeasureInference(fd: inox.ast.Trees#FunDef, msg: String)
    extends Exception(msg)
}
