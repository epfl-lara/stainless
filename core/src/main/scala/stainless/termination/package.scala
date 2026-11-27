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

  /** The unrolling bound of the queries of the termination checker when the solvers have a
    * resource limit (`--z3-rlimit`, `--cvc5-rlimit`), see [[SolverProvider]]. */
  object optTerminationUnrollBound extends inox.IntOptionDef("termination-unroll-bound", 16, "<PosInt>")

  /** The resource limit of each check of the termination checker's queries, in millions of units,
    * when it is lower than that of the solvers (`--z3-rlimit`, `--cvc5-rlimit`), see [[SolverProvider]]. */
  object optTerminationRlimit extends inox.IntOptionDef("termination-rlimit", 5, "<PosInt>")

  object DebugSectionTermination extends inox.DebugSection("termination")

  case class FailedMeasureInference(fd: inox.ast.Trees#FunDef, msg: String)
    extends Exception(msg)
}
