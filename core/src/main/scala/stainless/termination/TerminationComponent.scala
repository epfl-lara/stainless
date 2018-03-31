/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.Future
import scala.util.{ Success, Failure }

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

  override def apply(funs: Seq[Identifier], p: TerminationProgram, ctx: inox.Context): Future[Analysis] = {
    import p._
    import p.trees._
    import p.symbols._
    import ctx._

    val c = TerminationChecker(p, ctx)

    val res = funs map { id =>
      val fd = getFunction(id)
      val (time, tryStatus) = timers.termination.runAndGetTime { c.terminates(fd) }
      tryStatus match {
        case Success(status) => fd -> (status, time)
        case Failure(e) => reporter.internalError(e)
      }
    }

    Future.successful(new TerminationAnalysis {
      override val checker: c.type = c
      override val results: Map[p.trees.FunDef, (c.TerminationGuarantee, Long)] = res.toMap
      override val sources = funs.toSet
    })
  }
}

