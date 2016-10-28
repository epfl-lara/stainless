/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import solvers._
import inox.utils.ASCIIHelpers._

object VerificationComponent extends SimpleComponent {
  val name = "verification"
  val description = "Verification of function contracts"

  val trees: stainless.trees.type = stainless.trees

  val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  implicit val debugSection = DebugSectionVerification

  trait VerificationReport extends Report { self =>
    val program: Program { val trees: stainless.trees.type }
    val results: Map[VC[program.trees.type], VCResult[program.trees.type]]

    import program._

    lazy val vrs = results.toSeq.sortBy { case (vc, _) => (vc.fd.name, vc.kind.toString) }

    lazy val totalConditions = vrs.size
    lazy val totalTime = vrs.map(_._2.time.getOrElse(0l)).sum
    lazy val totalValid = vrs.count(_._2.isValid)
    lazy val totalInvalid = vrs.count(_._2.isInvalid)
    lazy val totalUnknown = vrs.count(_._2.isInconclusive)

    def emit(): Unit = {
      if (totalConditions > 0) {
        var t = Table("Verification Summary")

        t ++= vrs.map { case (vc, vr) =>
          Row(Seq(
            Cell(vc.fd),
            Cell(vc.kind.name),
            Cell(vc.getPos),
            Cell(vr.status),
            Cell(vr.solver.map(_.name).getOrElse("")),
            Cell(vr.time.map(t => f"${t/1000d}%3.3f").getOrElse(""))
          ))
        }

        t += Separator

        t += Row(Seq(
          Cell(f"total: $totalConditions%-4d   valid: $totalValid%-4d   invalid: $totalInvalid%-4d   unknown: $totalUnknown%-4d", 5),
          Cell(f"${totalTime/1000d}%7.3f", align = Right)
        ))

        ctx.reporter.info(t.render)
      } else {
        ctx.reporter.info("No verification conditions were analyzed.")
      }
    }
  }

  def check(funs: Seq[Identifier], p: StainlessProgram): Map[VC[p.trees.type], VCResult[p.trees.type]] = {
    val np = p.transform(new AssertionInjector {
      val s: p.trees.type = p.trees
      val t: p.trees.type = p.trees
      val symbols: p.symbols.type = p.symbols
    })

    import np._
    import np.trees._
    import np.symbols._

    val toVerify = funs.sortBy(getFunction(_).getPos)

    for (id <- toVerify) {
      if (getFunction(id).flags contains "library") {
        // FIXME: qualified name of `id`
        ctx.reporter.warning("Forcing verification of " + id + " which was assumed verified")
      }
    }

    VerificationChecker.verify(np)(funs)
  }

  def apply(funs: Seq[Identifier], p: StainlessProgram): VerificationReport = {
    val res = check(funs, p)

    new VerificationReport {
      val program: p.type = p
      val results = res
    }
  }
}
