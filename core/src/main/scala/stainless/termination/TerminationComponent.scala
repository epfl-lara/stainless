/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import inox.utils.ASCIIHelpers._
import stainless.utils.JsonConvertions._

import org.json4s.JsonDSL._
import org.json4s.JsonAST._

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

  trait TerminationAnalysis extends AbstractAnalysis {
    val checker: TerminationChecker {
      val program: Program { val trees: termination.trees.type }
    }

    import checker._
    import context._
    import program._
    import program.trees._

    type Duration = Long
    type Record = (TerminationGuarantee, Duration)
    val results: Map[FunDef, Record]

    override val name: String = TerminationComponent.this.name

    override type Report = TerminationReport

    override def toReport = new TerminationReport(results.toSeq map { case (fd, (g, time)) =>
      TextRecord(fd.id, fd.getPos, time, status(g), verdict(g, fd), kind(g))
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

    private def status(g: TerminationGuarantee): TerminationStatus = g match {
      case checker.NoGuarantee => Unknown
      case checker.Terminates(_) => Terminating
      case _ => NonTerminating
    }

  }

  sealed abstract class TerminationStatus {
    def isUnknown = this == Unknown
    def isTerminating = this == Terminating
    def isNonTerminating = this == NonTerminating

    def toText = this match {
      case Unknown => "unknown"
      case Terminating => "terminating"
      case NonTerminating => "non-terminating"
    }
  }

  object TerminationStatus {
    def parse(json: JValue) = json match {
      case JString("unknown") => Unknown
      case JString("terminating") => Terminating
      case JString("non-terminating") => NonTerminating
      case _ => ???
    }
  }

  case object Unknown extends TerminationStatus
  case object Terminating extends TerminationStatus
  case object NonTerminating extends TerminationStatus

  case class TextRecord(
    fid: Identifier, pos: inox.utils.Position, time: Long,
    status: TerminationStatus, verdict: String, kind: String
  )

  // Variant of the report without the checker, where all the data is mapped to text
  class TerminationReport(val results: Seq[TextRecord]) extends AbstractReport[TerminationReport] {
    override val name: String = TerminationComponent.this.name

    override def ~(other: TerminationReport): TerminationReport = {
      def buildMapping(subs: Seq[TextRecord]): Map[Identifier, Seq[TextRecord]] = subs groupBy { _.fid }

      val prev = buildMapping(this.results)
      val next = buildMapping(other.results)

      val fused = (prev ++ next).values.fold(Seq.empty)(_ ++ _)

      new TerminationReport(results = fused)
    }

    override def invalidate(ids: Seq[Identifier]) =
      new TerminationReport(results filterNot { ids contains _.fid })

    override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = if (results.isEmpty) None else {
      val rows = for { TextRecord(fid, pos, time, status, verdict, kind) <- results } yield Row(Seq(
        Cell(fid.name),
        Cell((if (status.isTerminating) "\u2713" else "\u2717") + " " + verdict),
        Cell(f"${time / 1000d}%3.3f")
      ))

      val valid = results count { _.status.isTerminating }
      val validFromCache = 0
      val invalid = results count { _.status.isNonTerminating }
      val unknown = results count { _.status.isUnknown }
      val time = (results map { _.time }).sum

      val stats = ReportStats(results.size, time, valid, validFromCache, invalid, unknown)

      Some((rows, stats))
    }

    override def emitJson: JArray = for { TextRecord(fid, pos, time, status, verdict, kind) <- results } yield {
      ("fd" -> fid.name) ~
      ("_fid" -> fid.toJson) ~
      ("pos" -> pos.toJson) ~
      ("kind" -> kind) ~ // brief
      ("verdict" -> verdict) ~ // detailed
      ("status" -> status.toText) ~
      ("time" -> time)
    }

  }

  object TerminationReport {
    def parse(json: JValue): TerminationReport = {
      val records = for {
        JArray(records) <- json
        record <- records
      } yield {
        val fid = parseIdentifier(record \ "_fid")
        val pos = parsePosition(record \ "pos")
        val JInt(time) = record \ "time"
        val JString(kind) = record \ "kind"
        val JString(verdict) = record \ "verdict"
        val status = TerminationStatus.parse(record \ "status")

        TextRecord(fid, pos, time.longValue, status, verdict, kind)
      }

      new TerminationReport(records)
    }
  }


  override def apply(funs: Seq[Identifier], p: Program { val trees: termination.trees.type }, ctx: inox.Context): TerminationAnalysis = {
    import p._
    import p.trees._
    import p.symbols._
    import ctx._

    val c = TerminationChecker(p, ctx)

    val toVerify = funs.map(getFunction(_)).sortBy(_.getPos)

    for (fd <- toVerify)  {
      if (fd.flags contains "library") {
        val fullName = fd.id.fullName
        reporter.warning(s"Forcing termination checking of $fullName which was assumed terminating")
      }
    }

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
