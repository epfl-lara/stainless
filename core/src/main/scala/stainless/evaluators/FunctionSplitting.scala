/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package evaluators

trait FunctionSplitting extends inox.ast.ProgramTransformer {

  val maxSize: Int

  lazy val targetProgram: inox.Program { val trees: sourceProgram.trees.type } = new inox.Program {
    val trees: sourceProgram.trees.type = sourceProgram.trees
    val ctx = sourceProgram.ctx
    import trees._

    private def split(fd: FunDef): Seq[FunDef] = {
      import sourceProgram.symbols._

      var fds: Seq[FunDef] = Seq.empty

      def rec(e: Expr): (Expr, Int) = e match {
        case (_: Choose) | (_: Forall) | (_: Lambda) => (e, exprOps.formulaSize(e))
        case Operator(es, recons) =>
          val (nes, sizes) = es.map(rec).unzip
          val size = sizes.sum + 1
          if (size > maxSize) {
            val id = FreshIdentifier(fd.id.name + "_split", true)
            val tparams = fd.tparams.map(_.freshen)
            val tpMap = (fd.typeArgs zip tparams.map(_.tp)).toMap

            val closures = exprOps.variablesOf(e).toSeq
            val vars = closures.map(_.freshen)
            val varMap = (closures zip vars).toMap

            val params = vars.map(v => instantiateType(v, tpMap).asInstanceOf[Variable].toVal)
            val body = instantiateType(exprOps.replaceFromSymbols(varMap, recons(nes)), tpMap)

            fds :+= new FunDef(id, tparams, params, instantiateType(e.getType, tpMap), body, Set())
            (FunctionInvocation(id, fd.typeArgs, closures), 0)
          } else {
            (recons(nes), size)
          }
      }

      val newFd = fd.copy(fullBody = rec(fd.fullBody)._1)
      newFd +: fds
    }

    val symbols = NoSymbols
      .withADTs(sourceProgram.symbols.adts.values.toSeq)
      .withFunctions(sourceProgram.symbols.functions.values.toSeq.flatMap(split))
  }

  protected object encoder extends sourceProgram.trees.IdentityTreeTransformer
  protected object decoder extends sourceProgram.trees.IdentityTreeTransformer
}

object FunctionSplitting {
  def apply(p: Program, max: Int = 500): FunctionSplitting { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
    val maxSize: Int = max
  } with FunctionSplitting
}
