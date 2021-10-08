/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
import trees._

import TypeCheckerUtils._
import TypeCheckerContext._

import java.io.FileWriter

object TypeCheckerDerivation {

  sealed abstract class Judgment(val tc: TypingContext) extends inox.utils.Positioned {
    override def getPos = tc.getPos
    def asString(using opts: PrinterOptions, raw: Boolean = false): String
    def htmlClass: String
  }

  case class IsType(override val tc: TypingContext, t: Type) extends Judgment(tc) {
    override def asString(using opts: PrinterOptions, raw: Boolean = false) = {
      if (raw)
        s"⊢ ${t.asString} is a type"
      else
        s"⊢ ${typeColor(shortString(t.asString))} is a type"
    }
    def htmlClass = "isType"
  }

  case class CheckType(override val tc: TypingContext, e: Expr, t: Type) extends Judgment(tc) {
    override def asString(using opts: PrinterOptions, raw: Boolean = false) = (t, raw) match {
      case (TrueBoolean(), false) => s"⊢ ${termColor(shortString(e.asString))} is true"
      case (_, false) => s"⊢ ${termColor(shortString(e.asString))} ⇓ ${typeColor(shortString(t.asString))}"
      case (TrueBoolean(), true) => s"⊢ ${e.asString} is true"
      case (_, true) => s"⊢ ${e.asString} ⇓ ${t.asString}"
    }
    def htmlClass = "checkType"
  }

  case class InferType(override val tc: TypingContext, e: Expr, t: Type) extends Judgment(tc) {
    override def asString(using opts: PrinterOptions, raw: Boolean = false) = {
      if (raw)
        s"⊢ ${e.asString} ⇑ ${t.asString}"
      else
        s"⊢ ${termColor(shortString(e.asString))} ⇑ ${typeColor(shortString(t.asString))}"
    }
    def htmlClass = "inferType"
  }

  case class IsSubtype(override val tc: TypingContext, t1: Type, t2: Type) extends Judgment(tc) {
    override def asString(using opts: PrinterOptions, raw: Boolean = false) = {
      if (raw)
        s"⊢ ${t1.asString} <: ${t2.asString}"
      else
        s"⊢ ${typeColor(shortString(t1.asString))} <: ${typeColor(shortString(t2.asString))}"
    }
    def htmlClass = "isSubtype"
  }

  case class AreEqualTypes(override val tc: TypingContext, t1: Type, t2: Type) extends Judgment(tc) {
    override def asString(using opts: PrinterOptions, raw: Boolean = false) = {
      if (raw)
        s"⊢ ${t1.asString} =:= ${t2.asString}"
      else
        s"⊢ ${typeColor(shortString(t1.asString))} =:= ${typeColor(shortString(t2.asString))}"
    }
    def htmlClass = "areEqualTypes"
  }

  case class JVC(override val tc: TypingContext, e: Expr) extends Judgment(tc) {
    override def asString(using opts: PrinterOptions, raw: Boolean = false) = {
      if (raw)
        s"${e.asString} is true (VC: ${tc.vcKind})"
      else
        s"<span style='font-weight: bold'>⊢ ${termColor(shortString(e.asString))} is true (VC: ${tc.vcKind})</span>"
    }
    def htmlClass = "vc"
  }

  case class OKFunction(id: Identifier) extends Judgment(TypingContext.empty) {
    override def asString(using opts: PrinterOptions, raw: Boolean = false) = {
      if (raw)
        s"⊢ ${id.asString} OK"
      else
        s"⊢ ${termColor(id.asString)} OK"
    }
    def htmlClass = "okFun"
  }

  case class OKADT(id: Identifier) extends Judgment(TypingContext.empty) {
    override def asString(using opts: PrinterOptions, raw: Boolean = false) = {
      if (raw)
        s"⊢ ${id.asString} OK"
      else
        s"⊢ ${typeColor(id.asString)} OK"
    }
    def htmlClass = "okADT"
  }

  case class NodeTree[T](node: T, children: Seq[NodeTree[T]])

  case class TyperResult(vcs: Seq[StainlessVC], trees: Seq[NodeTree[Judgment]]) {
    def ++(that: TyperResult) = {
      TyperResult(vcs ++ that.vcs, trees ++ that.trees)
    }

    def root(j: Judgment) = TyperResult(vcs, Seq(NodeTree(j, trees)))
  }

  object TyperResult {
    val valid = TyperResult(Seq(), Seq())
    def apply(l: Seq[TyperResult]): TyperResult = {
      l.foldLeft(TyperResult.valid)(_ ++ _)
    }
  }

  def prettyPrint(l: Seq[NodeTree[Judgment]], depth: Int)(using PrinterOptions): String = {
    "<ul style='list-style-type: none;'>\n" +
      l.map(t => prettyPrint(t, depth + 1)).mkString("\n") +
    "</ul>"
  }

  def prettyPrint(t: NodeTree[Judgment], depth: Int)(using opts: PrinterOptions): String = {
    val indentation = "  " * depth
    val childrenString = prettyPrint(t.children, depth + 1)
    indentation +
      s"<li> <span class='node ${t.node.htmlClass}'>" +
        s"${t.node.asString}" +
        s"""<span class=full-context><pre><code class="language-scala">${t.node.getPos.fullString}""" +
        s"\n\n${t.node.tc.asString()}\n\n" +
        s"${t.node.asString(using opts, raw = true)}" +
      "</code></pre></span></span>\n" +
      childrenString +
    indentation + "</li>"
  }

  def color(c: String, s: String) = s"<span style='color:$c'>$s</span>"
  def termColor(s: String) = color("#007c46", s)
  def typeColor(s: String) = color("#9b2600", s)

  def makeHTMLFile(fileName: String, trees: Seq[NodeTree[Judgment]])(using PrinterOptions): Unit = {
    val fw = new FileWriter(fileName)
    fw.write("<!DOCTYPE html>")
    fw.write("<html lang=\"en\">")
    fw.write("<head>\n")
    fw.write("<meta charset=\"UTF-8\">\n")
    fw.write("""<link rel="stylesheet"
                |     href="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/10.7.1/styles/default.min.css">
                |<script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/10.7.1/highlight.min.js"></script>""".stripMargin + "\n")
    fw.write("""<script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/10.7.1/languages/scala.min.js"></script>""" + "\n")
    fw.write("<script>hljs.highlightAll();</script>\n")
    fw.write("""|<style>
                |body {
                |  font-family: "Fira Code", Menlo, Monaco, monospace;
                |  background-color: white;
                |  color: black;
                |}
                |
                |.inferType {
                |  background-color: #f0f0ff
                |}
                |
                |.inferType:hover {
                |  background-color: #e0e0ee
                |}
                |
                |.checkType {
                |  background-color: #f0fff0
                |}
                |
                |.checkType:hover {
                |  background-color: #e0eee0
                |}
                |
                |.areEqualTypes {
                |  background-color: #feffc2
                |}
                |
                |.areEqualTypes:hover {
                |  background-color: #dadba7
                |}
                |
                |.isSubtype {
                |  background-color: #fff6eb
                |}
                |
                |.isSubtype:hover {
                |  background-color: #d4d492
                |}
                |
                |.isType {
                |  background-color: #fff6eb
                |}
                |
                |.isType:hover {
                |  background-color: #d4d492
                |}
                |
                |.vc {
                |  background-color: #ffeccf
                |}
                |
                |.vc:hover {
                |  background-color: #d9c8b0
                |}
                |
                |.okFun {
                |  background-color: #efd1ff
                |}
                |
                |.okFun:hover {
                |  background-color: #c9b0d6
                |}
                |
                |.okADT {
                |  background-color: #efd1ff
                |}
                |
                |.okADT:hover {
                |  background-color: #c9b0d6
                |}
                |
                |ul {
                |  list-style-type: none;
                |  padding-left: 10px;
                |}
                |
                |.node {
                |  position: relative;
                |}
                |
                |.node:hover > span.full-context {
                |  position: absolute;
                |  top: 10px;
                |  left: 30px;
                |  width: 70vw;
                |  max-height: 70vh;
                |  overflow-y: scroll;
                |  background-color: #a4d5de;
                |  word-wrap: break-word;
                |  z-index: 999999;
                |  display: block;
                |}
                |
                |.node > span.full-context {
                |  display: none;
                |}
                |
                |
                |</style>""".stripMargin)
    fw.write("</head>\n\n")

    fw.write("<body>\n")
    fw.write("""<script type="text/javascript" src="https://code.jquery.com/jquery-3.4.1.min.js"></script>""")
    fw.write("<script>\n")
    fw.write("""|$(document).ready(function () {
                |  $('.node').click(function(e) {
                |    if (!getSelection().toString()) {
                |      text = $(this).html()
                |      if (text.startsWith("(Folded) "))
                |        $(this).html(text.substring(9));
                |      else
                |        $(this).html("(Folded) " + text);
                |      $(this).parent().find("ul").toggle();
                |    }
                |  });
                |});
                |""".stripMargin)
    fw.write("</script>\n")
    fw.write(prettyPrint(trees, 0) + "\n")
    fw.write("</body>\n")
    fw.write("</html>")
    fw.close()
  }
}
