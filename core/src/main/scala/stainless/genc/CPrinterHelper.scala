/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import CAST.Tree

/* Printer helpers adapted to C code generation */

case class PrinterContext(
  indent: Int,
  printer: CPrinter,
  previous: Option[Tree],
  current: Tree
)

object CPrinterHelpers {
  class Printable(val f: PrinterContext ?=> Any) {
    def print(ctx: PrinterContext) = f(using ctx)
  }

  implicit class PrinterHelper(val sc: StringContext) extends AnyVal {
    def c(args: Any*)(using ctx: PrinterContext): Unit = {
      val printer = ctx.printer
      val sb = printer.sb

      import printer.WrapperTree

      val strings     = sc.parts.iterator
      val expressions = args.iterator

      var extraInd = 0
      var firstElem = true

      while(strings.hasNext) {
        val s = strings.next().stripMargin

        // Compute indentation
        val start = s.lastIndexOf('\n')
        if(start >= 0 || firstElem) {
          var i = start + 1
          while(i < s.length && s(i) == ' ') {
            i += 1
          }
          extraInd = (i - start - 1) / 2
        }

        firstElem = false

        // Make sure new lines are also indented
        sb.append(s.replaceAll("\n", "\n" + ("  " * ctx.indent)))

        val nctx = ctx.copy(indent = ctx.indent + extraInd)

        if (expressions.hasNext) {
          val e = expressions.next()

          e match {
            case ts: Seq[Any] =>
              nary(ts).print(nctx)

            case t: Tree =>
              val nctx2 = nctx.copy(current = t, previous = Some(nctx.current))
              printer.pp(t)(using nctx2)

            case wt: WrapperTree =>
              printer.pp(wt)(using nctx)

            case p: Printable =>
              p.print(nctx)

            case e =>
              sb.append(e.toString)
          }
        }
      }
    }
  }

  def nary(ls: Seq[Any], sep: String = ", ", opening: String = "", closing: String = ""): Printable = Printable {
    val (o, c) = if (ls.isEmpty) ("", "") else (opening, closing)
    val strs = o +: List.fill(ls.size-1)(sep) :+ c
    new StringContext(strs: _*).c(ls: _*)
  }

}
