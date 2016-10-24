/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import inox.utils.ASCIIHelpers._

object TerminationComponent extends SimpleComponent {
  val name = "termination"
  val description = "Check program termination."

  val trees: termination.trees.type = termination.trees

  val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees

    override def transform(e: s.Expr): t.Expr = e match {
      case s.Decreases(rank, body) => transform(body)
      case _ => super.transform(e)
    }
  })

  def apply(funs: Seq[Identifier], p: Program { val trees: termination.trees.type }): Unit = {
    import p._
    import p.trees._
    import p.symbols.{asString => _, _}

    val checker = TerminationChecker(p, ctx.options)

    val timer = ctx.timers.termination.start()

    val toVerify = (for {
      id <- funs
      fd = getFunction(id)
      if !(fd.flags contains "library")
    } yield fd).sortBy(_.getPos)

    val results = for (fd <- toVerify) yield fd -> checker.terminates(fd)

    val time = timer.stop()

    // output the report

    var t = Table("Termination Summary")

    for ((fd, g) <- results) t += Row(Seq(
      Cell(asString(fd.id)),
      Cell {
        val result = if (g.isGuaranteed) "\u2713" else "\u2717"
        val verdict = g match {
          case checker.LoopsGivenInputs(reason, args) =>
            s"Non-terminating for call: ${asString(fd.id)}(${args.map(_.asString).mkString(",")})"
          case checker.MaybeLoopsGivenInputs(reason, args) =>
            s"Possibly non-terminating for call: ${asString(fd.id)}(${args.map(_.asString).mkString(",")})"
          case checker.CallsNonTerminating(fds) =>
            s"Calls non-terminating functions: ${fds.map(fd => asString(fd.id)).mkString(",")}"
          case checker.Terminates(reason) =>
            s"Terminates ($reason)"
          case checker.NoGuarantee =>
            "No guarantee"
        }
        s"$result $verdict"
      }
    ))

    t += Separator

    t += Row(Seq(Cell(
      f"Analysis time: $time%7.3f",
      spanning = 2
    )))

    ctx.reporter.info(t.render)
  }
}
