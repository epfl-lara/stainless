/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import inox.utils.ASCIIHelpers._

object TerminationComponent extends SimpleComponent {
  val name = "termination"
  val description = "Check program termination."

  val trees: termination.trees.type = termination.trees

  type Report = TerminationReport

  object lowering extends inox.ast.SymbolTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees

    override def transform(syms: s.Symbols): t.Symbols = {
      syms.transform(new ast.TreeTransformer {
        val s: extraction.trees.type = extraction.trees
        val t: extraction.trees.type = extraction.trees

        override def transform(e: s.Expr): t.Expr = e match {
          case s.Decreases(rank, body) =>
            val trank = transform(rank)
            val es = rank.getType(syms) match {
              case s.TupleType(tps) => tps.indices.map(i => t.TupleSelect(trank, i + 1))
              case _ => Seq(trank)
            }

            t.Assert(
              t.andJoin(es.map(e => t.GreaterEquals(e, t.IntegerLiteral(0)))),
              Some("Measure not guaranteed positive"),
              transform(body)
            ).copiedFrom(e)

          case _ => super.transform(e)
        }
      })
    }
  }

  trait TerminationReport extends AbstractReport {
    val checker: TerminationChecker {
      val program: Program { val trees: termination.trees.type }
    }

    import checker._
    import program._
    import program.trees._

    val results: Map[FunDef, TerminationGuarantee]

    val time: Long

    def emit(): Unit = {
      var t = Table("Termination Summary")

      for ((fd, g) <- results.toSeq.sortBy(_._1.getPos)) t += Row(Seq(
        Cell(fd.id.asString),
        Cell {
          val result = if (g.isGuaranteed) "\u2713" else "\u2717"
          val verdict = g match {
            case checker.LoopsGivenInputs(reason, args) =>
              s"Non-terminating for call: ${fd.id.asString}(${args.map(_.asString).mkString(",")})"
            case checker.MaybeLoopsGivenInputs(reason, args) =>
              s"Possibly non-terminating for call: ${fd.id.asString}(${args.map(_.asString).mkString(",")})"
            case checker.CallsNonTerminating(fds) =>
              s"Calls non-terminating functions: ${fds.map(_.id.asString).mkString(",")}"
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
        f"Analysis time: ${time/1000d}%7.3f",
        spanning = 2
      )))

      ctx.reporter.info(t.render)
    }
  }

  def apply(funs: Seq[Identifier], p: Program { val trees: termination.trees.type }): TerminationReport = {
    import p._
    import p.trees._
    import p.symbols._

    val c = TerminationChecker(p, ctx.options)

    val timer = ctx.timers.termination.start()

    val toVerify = for {
      id <- funs
      fd = getFunction(id)
      if !(fd.flags contains "library")
    } yield fd

    val res = for (fd <- toVerify) yield fd -> c.terminates(fd)
    val t = timer.stop()

    new TerminationReport {
      val checker: c.type = c
      val results = res.toMap
      val time = t
    }
  }
}
