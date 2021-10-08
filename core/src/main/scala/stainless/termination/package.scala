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

  object DebugSectionTermination extends inox.DebugSection("termination")

  case class FailedMeasureInference(fd: inox.ast.Trees#FunDef, msg: String)
    extends Exception(msg)
}
