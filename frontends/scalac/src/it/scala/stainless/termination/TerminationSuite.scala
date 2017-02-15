/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.duration._

class TerminationSuite extends ComponentTestSuite with inox.ResourceUtils {

  val component = TerminationComponent

  override protected def optionsString(options: inox.Options): String = {
    "solver=" + options.findOptionOrDefault(inox.optSelectedSolvers).head
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    case "termination/valid/NNF" => Skip
    case "verification/valid/Nested14" => Ignore
    // smt-z3 crashes on some permutations of the MergeSort2 problem encoding due to Bags...
    case "verification/valid/MergeSort2" => WithContext(ctx.copy(options = ctx.options + optIgnorePosts(true)))
    case _ => super.filter(ctx, name)
  }

  testAll("termination/valid") { (report, _) =>
    val failures = report.results.collect { case (fd, guarantee) if !guarantee.isGuaranteed => fd }
    assert(failures.isEmpty, "Functions " + failures.map(_.id) + " should terminate")
  }

  testAll("verification/valid") { (report, _) =>
    val failures = report.results.collect { case (fd, guarantee) if !guarantee.isGuaranteed => fd }
    assert(failures.isEmpty, "Functions " + failures.map(_.id) + " should terminate")
  }

  testAll("termination/looping") { (report, _) =>
    val looping = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("looping") }
    val notLooping = looping.filterNot(_._2.isInstanceOf[report.checker.NonTerminating])
    assert(notLooping.isEmpty, "Functions " + notLooping.map(_._1.id) + " should not terminate")

    val calling = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("calling") }
    val notCalling = calling.filterNot(_._2.isInstanceOf[report.checker.CallsNonTerminating])
    assert(notCalling.isEmpty, "Functions " + notCalling.map(_._1.id) + " should call non-terminating")

    val guaranteed = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("ok") }
    val notGuaranteed = guaranteed.filterNot(_._2.isGuaranteed)
    assert(notGuaranteed.isEmpty, "Functions " + notGuaranteed.map(_._1.id) + " should terminate")
  }
}
