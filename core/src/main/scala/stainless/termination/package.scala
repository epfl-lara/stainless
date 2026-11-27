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
    * limit (`--z3-rlimit`, `--cvc5-rlimit`), as a factor of a number of millions of resource units per
    * check for each solver and of [[TerminationWork.baseUnrollBound]] unrollings, see [[SolverProvider]]. */
  object optTerminationWork extends inox.DoubleOptionDef("termination-work", 1.0, "<PosDouble>")

  object TerminationWork {
    // The resource units of z3 and cvc5 measure different work: on the same queries, cvc5 counts about
    // as many as z3 on small ones and 10 to 100 times fewer on hard ones. Each base is the work that
    // keeps `TerminationSuite` passing with the solver: cvc5 passes with any limit from 1 million.
    val baseZ3Rlimit: Int = 5
    val baseCVC5Rlimit: Int = 1
    // `Float8` needs 8 unrollings for measure inference to find its measure
    val baseUnrollBound: Int = 8

    private def scaled(base: Int, work: Double): Int = (base * work).round.toInt max 1

    /** The resource limits of each check of z3 and of cvc5, in millions of units, for the given work factor. */
    def z3Rlimit(work: Double): Int = scaled(baseZ3Rlimit, work)
    def cvc5Rlimit(work: Double): Int = scaled(baseCVC5Rlimit, work)

    /** The unrolling bound of each query for the given work factor. */
    def unrollBound(work: Double): Int = scaled(baseUnrollBound, work)
  }

  object DebugSectionTermination extends inox.DebugSection("termination")

  case class FailedMeasureInference(fd: inox.ast.Trees#FunDef, msg: String)
    extends Exception(msg)
}
