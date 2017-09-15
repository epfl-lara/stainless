/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

object TerminationComponent extends SimpleComponent {
  override val name = "termination"
  override val description = "Check program termination."

  override val trees: termination.trees.type = termination.trees

  override type Analysis = TerminationAnalysis

  override object lowering extends inox.ast.SymbolTransformer {
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
              t.andJoin(es.map(e => t.GreaterEquals(e, e.getType(syms) match {
                case s.BVType(size) => t.BVLiteral(0, size)
                case s.IntegerType() => t.IntegerLiteral(0)
                case _ => throw inox.FatalError("Unexpected measure type for " + e)
              }))),
              Some("Measure not guaranteed positive"),
              transform(body)
            ).copiedFrom(e)

          case _ => super.transform(e)
        }
      })
    }
  }

  type TerminationProgram = Program { val trees: termination.trees.type }

  trait TerminationAnalysis extends AbstractAnalysis {
    val checker: TerminationChecker {
      val program: TerminationProgram
    }

    import checker._
    import context._
    import program._
    import program.trees._

    type Duration = Long
    type Record = (TerminationGuarantee, Duration)
    val results: Map[FunDef, Record]

    override val name: String = TerminationComponent.name

    override type Report = TerminationReport

    override def toReport = new TerminationReport(results.toSeq map { case (fd, (g, time)) =>
      TerminationReport.Record(fd.id, fd.getPos, time, status(g), verdict(g, fd), kind(g))
    })

    private def kind(g: TerminationGuarantee): String = g match {
      case checker.LoopsGivenInputs(_, _) => "non-terminating loop"
      case checker.MaybeLoopsGivenInputs(_, _) => "possibly non-terminating loop"
      case checker.CallsNonTerminating(_) => "non-terminating call"
      case checker.DecreasesFailed => "failed decreases check"
      case checker.Terminates(_) => "terminates"
      case checker.NoGuarantee => "no guarantee"
    }

    private def verdict(g: TerminationGuarantee, fd: FunDef): String = g match {
      case checker.LoopsGivenInputs(reason, args) =>
        s"Non-terminating for call: ${fd.id.asString}(${args.map(_.asString).mkString(",")})"
      case checker.MaybeLoopsGivenInputs(reason, args) =>
        s"Possibly non-terminating for call: ${fd.id.asString}(${args.map(_.asString).mkString(",")})"
      case checker.CallsNonTerminating(fds) =>
        s"Calls non-terminating functions: ${fds.map(_.id.asString).mkString(",")}"
      case checker.DecreasesFailed =>
        s"Failed decreases check"
      case checker.Terminates(reason) =>
        s"Terminates ($reason)"
      case checker.NoGuarantee =>
        "No guarantee"
    }

    private def status(g: TerminationGuarantee): TerminationReport.Status = g match {
      case checker.NoGuarantee => TerminationReport.Unknown
      case checker.Terminates(_) => TerminationReport.Terminating
      case _ => TerminationReport.NonTerminating
    }

  }

  override def apply(funs: Seq[Identifier], p: TerminationProgram, ctx: inox.Context): TerminationAnalysis = {
    import p._
    import p.trees._
    import p.symbols._
    import ctx._

    val c = TerminationChecker(p, ctx)

    val toVerify = funs.map(getFunction(_)).sortBy(_.getPos)

    for {
      fd <- toVerify
      if fd.flags contains "library"
      fullName <- fd.id.fullName
    } reporter.warning(s"Forcing termination checking of $fullName which was assumed terminating")

    val res = toVerify map { fd =>
      val timer = ctx.timers.termination.start()
      try {
        val status = c.terminates(fd)
        val time = timer.stop()

        fd -> (status, time)
      } finally {
        if (timer.isRunning) timer.stop()
      }
    }

    new TerminationAnalysis {
      override val checker: c.type = c
      override val results: Map[p.trees.FunDef, (c.TerminationGuarantee, Long)] = res.toMap
    }
  }
}

