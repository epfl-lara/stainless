/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import extraction.throwing.trees._

/*
 * Find the main & _main functions and perform a few sanity checks.
 *
 * This phase checks that:
 *  - there is only one main unit;
 *  - the main function is uniquely defined as a non-generic external function;
 *  - the _main function is uniquely defined as a non-generic, parameterless function;
 *  - _main return type is either Unit or Int.
 */
private[genc] object ExtractEntryPointPhase extends LeonPipeline[Symbols, Definition] {
  val name = "Compute main function dependencies"
  val description = "Check validity of main & _main functions, and identify their dependencies"

  def getTimer(ctx: inox.Context) = ctx.timers.genc.get("extract main")

  def run(ctx: inox.Context, syms: Symbols): FunDef = {
    import ExtraOps._

    // val mainUnit = {
    //   val mainUnits = prog.units filter { _.isMainUnit }

    //   // Make sure exactly one main unit is defined -- this is just a sanity check
    //   if (mainUnits.size == 0) fatalError("No main unit in the program")
    //   if (mainUnits.size >= 2) fatalError("Multiple main units in the program")

    //   mainUnits.head
    // }

    // def getFunDef(name: String): FunDef = {
    //   val results = mainUnit.definedFunctions filter { _.id.name == name }

    //   // Make sure there is no ambiguity about the name and that the function is defined
    //   if (results.size == 0) fatalError(s"No $name was defined in unit ${mainUnit.id.uniqueName}")
    //   if (results.size == 2) fatalError(s"Multiple $name were defined in unit ${mainUnit.id}")

    //   results.head
    // }

    val mainFd = syms.functions.values.find(fd => fd.id.name == "main").getOrElse(
      ctx.reporter.fatalError("No `main` function found")
    )
    val _mainFd = syms.functions.values.find(fd => fd.id.name == "_main").getOrElse(
      ctx.reporter.fatalError("No `_main` function found")
    )

    // Checks that "main" is properly defined
    if (mainFd.isGeneric)
      ctx.reporter.fatalError(mainFd.getPos, "The main function should not be generic")

    if (!mainFd.isExtern)
      ctx.reporter.fatalError(mainFd.getPos, "It is expected for `main(args)` to be extern")

    // Idem for "_main"
    if (_mainFd.params.size > 0)
      ctx.reporter.fatalError(_mainFd.getPos, "_main() should have no parameter")

    if (_mainFd.isGeneric)
      ctx.reporter.fatalError(_mainFd.getPos, "_main() should not be generic")

    if (_mainFd.isExtern)
      ctx.reporter.fatalError(_mainFd.getPos, "_main() should not be extern")

    _mainFd.returnType match {
      case UnitType() | Int32Type() => // valid
      case _ => ctx.reporter.fatalError(_mainFd.getPos, "_main() should either return an integer or nothing")
    }

    _mainFd
  }
}
