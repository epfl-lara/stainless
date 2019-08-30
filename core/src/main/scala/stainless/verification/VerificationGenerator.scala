/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

trait VerificationGenerator { self =>
  val program: Program

  import program._
  import program.symbols._
  import program.trees._
  import CallGraphOrderings._

  type VC = verification.VC[program.trees.type]

  protected def getTactic(fd: FunDef): Tactic { val program: self.program.type }

  def generateVCs(funs: Seq[Identifier]): Seq[VC] = {
    val vcs: Seq[VC] = (for (id <- funs) yield {
      val fd = getFunction(id)
      val tactic = getTactic(fd)

      if (fd.body.isDefined) {
        tactic.generateVCs(id)
      } else {
        Nil
      }
    }).flatten

    vcs.sortBy(vc => (getFunction(vc.fd),
      if (vc.kind.underlying == VCKind.Precondition) 0
      else if (vc.kind.underlying == VCKind.Assert) 1
      else 2
    ))
  }

}

object VerificationGenerator {

  def gen(p: StainlessProgram, ctx: inox.Context)(funs: Seq[Identifier]): Seq[VC[p.trees.type]] = {
    object generator extends VerificationGenerator {
      val program: p.type = p

      protected def getTactic(fd: p.trees.FunDef) = DefaultTactic(p, ctx)
    }

    generator.generateVCs(funs)
  }

}
