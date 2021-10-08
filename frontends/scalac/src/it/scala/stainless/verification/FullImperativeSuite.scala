/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.Await
import scala.concurrent.duration._
import extraction.xlang.{ TreeSanitizer, trees => xt }

class FullImperativeSuite extends ComponentTestSuite with inox.MainHelpers {

  override def configurations = super.configurations.map {
    seq => Seq(
      extraction.imperative.optFullImperative(true),
      optFailEarly(true),
      inox.optTimeout(75)
    ) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = ""

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // FIXME(gsps): Incomplete
    case "full-imperative/valid/CellDataStructuresAndRepr" => Skip
    // FIXME(gsps): Time-out?
    case "full-imperative/invalid/OpaqueEffectsGeneric" => Skip

    // FIXME(gsps): Works, but slow
    case "full-imperative/valid/TreeImmutMap" => Skip
    // FIXME(gsps): Works, but flaky on CI?
    case "full-imperative/valid/TreeImmutMapGeneric" => Skip

    case _ => super.filter(ctx, name)
  }

  override val component: VerificationComponent.type = VerificationComponent

  // This method was copied from the super class and overriden to filter out the 'copy' method from the extracted symbols,
  // since it involves allocations, and that isn't supported yet.
  // TODO: when allocation is supported, remove that overriden implementation.
  override def testAll(dir: String, recursive: Boolean = false)(block: (component.Analysis, inox.Reporter) => Unit): Unit = {
    require(dir != null, "Function testAll must be called with a non-null directory string")
    val fs = resourceFiles(dir, _.endsWith(".scala"), recursive).toList

    // Toggle this variable if you need to debug one specific test.
    // You might also want to run `it:testOnly *<some test suite>* -- -z "<some test filter>"`.
    val DEBUG = false

    if (DEBUG) {
      for {
        file <- fs.sortBy(_.getPath)
        path = file.getPath
        name = file.getName stripSuffix ".scala"
      } test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { ctx ?=>
        val (structure, program) = loadFiles(Seq(path))
        assert((structure count { _.isMain }) == 1, "Expecting only one main unit")
        val errors = TreeSanitizer(xt).enforce(program.symbols)
        if (!errors.isEmpty) {
          ctx.reporter.fatalError("There were errors in TreeSanitizer")
        }

        program.symbols.ensureWellFormed

        val run = component.run(extraction.pipeline)

        val exProgram = inox.Program(run.trees)(run extract program.symbols)
        exProgram.symbols.ensureWellFormed
        assert(ctx.reporter.errorCount == 0, "There were errors during extraction")

        val unit = structure.find(_.isMain).get
        assert(unit.id.name == name, "Expecting compilation unit to have same name as source file")

        val defs = inox.utils.fixpoint { (defs: Set[Identifier]) =>
          def derived(flags: Seq[run.trees.Flag]): Boolean =
            (defs & flags.collect { case run.trees.Derived(Some(id)) => id }.toSet).nonEmpty

          defs ++
          exProgram.symbols.functions.values.filter(fd => derived(fd.flags)).map(_.id) ++
          exProgram.symbols.sorts.values.filter(sort => derived(sort.flags)).map(_.id)
        } (unit.allFunctions(using program.symbols).toSet ++ unit.allClasses)

        val funs = defs.filter(exProgram.symbols.functions contains _).toSeq.filterNot(_.name.startsWith("copy")) // we filter out the copy methods

        val report = Await.result(run.execute(funs, exProgram.symbols), Duration.Inf)
        block(report, ctx.reporter)
      }
    } else {
      given ctx: inox.Context = inox.TestContext.empty
      val (structure, program) = loadFiles(fs.map(_.getPath))
      program.symbols.ensureWellFormed

      // We use a shared run during extraction to ensure caching of extraction results is enabled.

      for {
        unit <- structure
        if unit.isMain
        name = unit.id.name
      } test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { ctx ?=>
        val defs = (unit.allFunctions(using program.symbols).toSet ++ unit.allClasses).filterNot(_.name.startsWith("copy")) // we filter out the copy methods

        val deps = defs.flatMap(id => program.symbols.dependencies(id) + id)
        val symbols = extraction.xlang.trees.NoSymbols
          .withClasses(program.symbols.classes.values.filter(cd => deps(cd.id)).toSeq)
          .withFunctions(program.symbols.functions.values.filter(fd => deps(fd.id)).toSeq)
          .withTypeDefs(program.symbols.typeDefs.values.filter(td => deps(td.id)).toSeq)

        val extractor = component.run(extraction.pipeline)
        val exSymbols = extractor extract symbols
        exSymbols.ensureWellFormed
        assert(ctx.reporter.errorCount == 0, "There were errors during pipeline extraction")

        val run = component.run(extraction.pipeline)

        val funs = inox.utils.fixpoint { (defs: Set[Identifier]) =>
          def derived(flags: Seq[extractor.trees.Flag]): Boolean =
            (defs & flags.collect { case extractor.trees.Derived(Some(id)) => id }.toSet).nonEmpty

          defs ++
          exSymbols.functions.values.filter(fd => derived(fd.flags)).map(_.id) ++
          exSymbols.sorts.values.filter(sort => derived(sort.flags)).map(_.id)
        } (defs).toSeq.filter(exSymbols.functions contains _)

        // We have to cast the extracted symbols type as we are using two different
        // run instances. However, the trees types are the same so this should be safe (tm).
        val report = Await.result(
          run.execute(funs, exSymbols.asInstanceOf[run.trees.Symbols]),
          Duration.Inf
        )

        block(report, ctx.reporter)
      }
    }
  }

  testAll("full-imperative/valid") { (report, reporter) =>
    for ((vc, vr) <- report.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  testAll("full-imperative/invalid") { (analysis, _) =>
    val report = analysis.toReport
    assert(report.totalInvalid > 0, "There should be at least one invalid verification condition.")
  }
}
