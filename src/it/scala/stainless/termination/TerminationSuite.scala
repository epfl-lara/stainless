/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

class TerminationSuite extends ComponentTestSuite with inox.ResourceUtils {

  val component = TerminationComponent

  protected def mkTests(dir: String)(block: TerminationComponent.TerminationReport => Unit): Unit = {
    val fs = resourceFiles(s"regression/$dir", _.endsWith(".scala")).toList

    val (funss, program) = extract(fs.map(_.getPath))

    for ((name, funs) <- funss) {
      test(s"$dir/$name") { ctx =>
        val newProgram = program.withContext(ctx)
        val report = TerminationComponent.apply(funs, newProgram)
        block(report)
      }
    }
  }

  mkTests("termination/valid") { report =>
    val failures = report.results.collect { case (fd, guarantee) if !guarantee.isGuaranteed => fd }
    assert(failures.isEmpty, "Functions " + failures.map(_.id) + " should terminate")
  }

  mkTests("verification/valid") { report =>
    val failures = report.results.collect { case (fd, guarantee) if !guarantee.isGuaranteed => fd }
    assert(failures.isEmpty, "Functions " + failures.map(_.id) + " should terminate")
  }

  mkTests("termination/looping") { report =>
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
