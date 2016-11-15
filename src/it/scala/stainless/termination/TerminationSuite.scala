/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

class TerminationSuite extends ComponentTestSuite with inox.ResourceUtils {

  val component = TerminationComponent

  override protected def optionsString(options: inox.Options): String = {
    "solver=" + options.findOptionOrDefault(inox.optSelectedSolvers).head
  }

  override val ignored = Set("verification/valid/Nested14")

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
