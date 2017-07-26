/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import inox.utils.ASCIIHelpers._
import stainless.utils.JsonConvertions._

import org.json4s.JsonDSL._
import org.json4s.JsonAST.{ JArray }

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
              t.andJoin(es.map(e => t.GreaterEquals(e, e.getType(syms) match {
                case s.BVType(size) => t.BVLiteral(0, size)
                case s.IntegerType => t.IntegerLiteral(0)
                case _ => throw new inox.FatalError("Unexpected measure type for " + e)
              }))),
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

    override val name = TerminationComponent.this.name

    override val width = 2

    override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = if (results.isEmpty) None else {
      val rows = for ((fd, g) <- results.toSeq.sortBy(_._1.getPos)) yield Row(Seq(
        Cell(fd.id.asString),
        Cell((if (g.isGuaranteed) "\u2713" else "\u2717") + " " + verdict(g, fd))
      ))

      val valid = results count { r => r._2.isGuaranteed }
      val invalid = 0
      val unknown = results.size - valid

      val stats = ReportStats(results.size, time, valid, invalid, unknown)

      Some((rows, stats))
    }

    override def emitJson: JArray = {
      def kind(g: TerminationGuarantee): String = g match {
        case checker.LoopsGivenInputs(_, _) => "non-terminating loop"
        case checker.MaybeLoopsGivenInputs(_, _) => "possibly non-terminating loop"
        case checker.CallsNonTerminating(_) => "non-terminating call"
        case checker.DecreasesFailed => "failed decreases check"
        case checker.Terminates(_) => "terminates"
        case checker.NoGuarantee => "no guarantee"
      }

      val report: JArray = for { (fd, g) <- results } yield {
        ("fd" -> fd.id.name) ~
        ("pos" -> fd.getPos.toJson) ~
        ("kind" -> kind(g)) ~ // brief
        ("verdict" -> verdict(g, fd)) ~ // detailed
        ("guarantee" -> g.isGuaranteed)
      }

      report
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

  }

  def apply(funs: Seq[Identifier], p: Program { val trees: termination.trees.type }): TerminationReport = {
    import p._
    import p.trees._
    import p.symbols._

    val c = TerminationChecker(p, ctx.options)

    val timer = ctx.timers.termination.start()

    val toVerify = funs.map(getFunction(_)).sortBy(_.getPos)

    for (fd <- toVerify)  {
      if (fd.flags contains "library") {
        val fullName = fd.id.fullName
        ctx.reporter.warning(s"Forcing termination checking of $fullName which was assumed terminating")
      }
    }

    val res = for (fd <- toVerify) yield fd -> c.terminates(fd)
    val t = timer.stop()

    new TerminationReport {
      val checker: c.type = c
      val results = res.toMap
      val time = t
    }
  }
}
