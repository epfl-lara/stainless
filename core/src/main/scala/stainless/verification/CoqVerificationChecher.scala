/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.solvers._

import scala.concurrent.Future

object DebugSectionCoq extends inox.DebugSection("coq")

trait CoqVerificationChecker { self =>
  val program: StainlessProgram
  val context: inox.Context

  import context._
  import program._
  import program.trees._
  import program.symbols._

  implicit val debugSection = DebugSectionCoq

  type VC = verification.VC[program.trees.type]
  val VC = verification.VC

  type VCStatus = verification.VCStatus[program.Model]

  type VCResult = verification.VCResult[program.Model]
  val VCResult = verification.VCResult

  def verify(funs: Seq[Identifier]) = {
    println("Program to translate")
    println(program.asString)
    println("End of Program")
    println("===============================")
    val (pLibCoq, pCoq) = CoqEncoder.transformProgram(program, context)
    val lib = CoqIO.writeToCoqFile(pLibCoq)
    val file = CoqIO.writeToCoqFile(pCoq)
    CoqIO.coqc(file, context)
    Future(new VerificationAnalysis {
      override val program: self.program.type = self.program
      override val sources = Set[stainless.Identifier]()
      override val results = Map[VC, VCResult]()
    })
  }
}

object CoqVerificationChecker {
  def verify(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context) = {
    object Checker extends CoqVerificationChecker {
      val program: p.type = p
      val context = ctx
    }
    Checker.verify(funs)
  }
}
