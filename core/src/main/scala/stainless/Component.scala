/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import inox.utils.ASCIIHelpers._
import org.json4s.JsonAST.JArray
import extraction.xlang.{trees => xt}
import scala.language.existentials

case class ReportStats(total: Int, time: Long, valid: Int, invalid: Int, unknown: Int) {
  def +(more: ReportStats) = ReportStats(
    total + more.total,
    time + more.time,
    valid + more.valid,
    invalid + more.invalid,
    unknown + more.unknown
  )
}

trait AbstractReport { self =>
  val name: String
  def emitJson: JArray

  protected def emitRowsAndStats: Option[(Seq[Row], ReportStats)]

  final def emit(ctx: inox.Context): Unit = emitTable match {
    case None => ctx.reporter.info("No verification conditions were analyzed.")
    case Some(t) => ctx.reporter.info(t.render)
  }

  def ~(other: AbstractReport) = new AbstractReport {
    assert(other.width == self.width)

    override val name = if (self.name == other.name) self.name else (self.name + " ~ " + other.name)

    override def emitJson: JArray = {
      val JArray(as) = self.emitJson
      val JArray(bs) = other.emitJson
      JArray(as ++ bs)
    }

    override val width = self.width

    override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = (self.emitRowsAndStats, other.emitRowsAndStats) match {
      case (None, None) => None
      case (a, None) => a
      case (None, b) => b
      case (Some((rowsA, statsA)), Some((rowsB, statsB))) => Some((rowsA ++ rowsB, statsA + statsB))
    }
  }

  protected val width: Int

  private def emitTable: Option[Table] = emitRowsAndStats map { case (rows, stats) =>
    var t = Table(s"$name summary")
    t ++= rows
    t += Separator
    t += Row(Seq(
      Cell(
        f"total: ${stats.total}%-4d   valid: ${stats.valid}%-4d   " +
        f"invalid: ${stats.invalid}%-4d   unknown: ${stats.unknown}%-4d  " +
        f"time: ${stats.time/1000d}%7.3f",
        spanning = width
      )
    ))

    t
  }
}

trait Component {
  val name: String
  val description: String

  type Report <: AbstractReport

  val lowering: inox.ast.SymbolTransformer {
    val s: extraction.trees.type
    val t: extraction.trees.type
  }

}

object optFunctions extends inox.OptionDef[Seq[String]] {
  val name = "functions"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

trait SimpleComponent extends Component { self =>
  val trees: ast.Trees
  import trees._

  def extract(program: Program { val trees: xt.type }): Program { val trees: self.trees.type } = {
    val checker = inox.ast.SymbolTransformer(new extraction.CheckingTransformer {
      val s: extraction.trees.type = extraction.trees
      val t: self.trees.type = self.trees
    })

    val lowering = MainHelpers.components.filterNot(_ == this).foldRight(checker) {
      (l, r) => l.lowering andThen r
    }

    extraction.extract(program).transform(lowering)
  }

  def apply(program: Program { val trees: xt.type }): Report = {
    val extracted = extract(program)
    import extracted._

    val relevant = symbols.functions.values.filterNot { fd =>
      (fd.flags contains "library") || (fd.flags contains "unchecked")
    }.map(_.id).toSeq

    val functions = ctx.options.findOption(optFunctions) match {
      case Some(names) => relevant.filter(id => names contains id.name)
      case None => relevant
    }

    apply(functions, extracted)
  }

  def apply(functions: Seq[Identifier], program: Program { val trees: self.trees.type }): Report
}
