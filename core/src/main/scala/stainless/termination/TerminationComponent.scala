/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package termination

import io.circe._

import scala.concurrent.Future
import scala.util.{ Success, Failure }

object TerminationComponent extends Component {
  override val name = "termination"
  override val description = "Check program termination."

  override type Report = TerminationReport
  override type Analysis = TerminationAnalysis

  override object lowering extends inox.transformers.SymbolTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees

    override def transform(syms: s.Symbols): t.Symbols = {
      syms.transform(new transformers.TreeTransformer {
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
                case s.BVType(signed, size) => t.BVLiteral(signed, 0, size)
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

  override def run(pipeline: extraction.StainlessPipeline)(implicit ctx: inox.Context) = {
    new TerminationRun(pipeline)
  }
}

class TerminationRun(override val pipeline: extraction.StainlessPipeline)
                    (override implicit val context: inox.Context) extends {
  override val component = TerminationComponent
  override val trees: termination.trees.type = termination.trees
} with ComponentRun {

  import component.{Report, Analysis}

  override def parse(json: Json): Report = TerminationReport.parse(json)

  private[stainless] def execute(functions: Seq[Identifier], symbols: trees.Symbols): Future[Analysis] = {
    import trees._
    import context._

    val p = inox.Program(trees)(symbols)
    val c = TerminationChecker(p, context)

    val res = functions map { id =>
      val fd = symbols.getFunction(id)
      val (time, tryStatus) = timers.termination.runAndGetTime { c.terminates(fd) }
      tryStatus match {
        case Success(status) => fd -> (status, time)
        case Failure(e) => reporter.internalError(e)
      }
    }

    Future.successful(new TerminationAnalysis {
      override val checker: c.type = c
      override val results: Map[p.trees.FunDef, (c.TerminationGuarantee, Long)] = res.toMap
      override val sources = functions.toSet
    })
  }
}

