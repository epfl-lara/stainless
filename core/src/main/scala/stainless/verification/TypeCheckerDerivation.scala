/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification
import trees._

import TypeCheckerUtils._
import TypeCheckerContext._

import java.io.FileWriter

object TypeCheckerDerivation {

  sealed abstract class Judgment(val tc: TypingContext) extends inox.utils.Positioned {
    override def getPos = tc.getPos
    def asString(implicit opts: PrinterOptions): String
  }

  case class IsType(override val tc: TypingContext, t: Type) extends Judgment(tc) {
    override def asString(implicit opts: PrinterOptions) = s"⊢ ${typeColor(shortString(t.asString))} is a type"
  }

  case class CheckType(override val tc: TypingContext, e: Expr, t: Type) extends Judgment(tc) {
    override def asString(implicit opts: PrinterOptions) = t match {
      case TrueBoolean() => s"⊢ ${termColor(shortString(e.asString))} is true"
      case _ => s"⊢ ${termColor(shortString(e.asString))} ⇓ ${typeColor(shortString(t.asString))}"
    }
  }

  case class InferType(override val tc: TypingContext, e: Expr, t: Type) extends Judgment(tc) {
    override def asString(implicit opts: PrinterOptions) = s"⊢ ${termColor(shortString(e.asString))} ⇑ ${typeColor(shortString(t.asString))}"
  }

  case class IsSubtype(override val tc: TypingContext, t1: Type, t2: Type) extends Judgment(tc) {
    override def asString(implicit opts: PrinterOptions) = s"⊢ ${typeColor(shortString(t1.asString))} <: ${typeColor(shortString(t2.asString))}"
  }

  case class AreEqualTypes(override val tc: TypingContext, t1: Type, t2: Type) extends Judgment(tc) {
    override def asString(implicit opts: PrinterOptions) = s"⊢ ${typeColor(shortString(t1.asString))} =:= ${typeColor(shortString(t2.asString))}"
  }

  case class JVC(override val tc: TypingContext, e: Expr) extends Judgment(tc) {
    override def asString(implicit opts: PrinterOptions) = s"<span style='font-weight: bold'>⊢ ${termColor(shortString(e.asString))} is true (VC: ${tc.vcKind})</span>"
  }

  case class OKFunction(id: Identifier) extends Judgment(TypingContext.empty) {
    override def asString(implicit opts: PrinterOptions) = s"⊢ ${termColor(id.asString)} OK"
  }

  case class OKADT(id: Identifier) extends Judgment(TypingContext.empty) {
    override def asString(implicit opts: PrinterOptions) = s"⊢ ${typeColor(id.asString)} OK"
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

  def prettyPrint(l: Seq[NodeTree[Judgment]], depth: Int)(implicit opts: PrinterOptions): String = {
    "<ul style='list-style-type: none;'>\n" +
      l.map(t => prettyPrint(t, depth + 1)).mkString("\n") +
    "</ul>"
  }

  def prettyPrint(t: NodeTree[Judgment], depth: Int)(implicit opts: PrinterOptions): String = {
    val indentation = "  " * depth
    val childrenString = prettyPrint(t.children, depth + 1)
    indentation + s"<li> <span title='${t.node.getPos.fullString}\n${t.node.tc.asString()}'> ${t.node.asString} </span>\n" +
      childrenString +
    indentation + "</li>"
  }

  def color(c: String, s: String) = s"<span style='color:$c'>$s</span>"
  def termColor(s: String) = color("#007c46", s)
  def typeColor(s: String) = color("#9b2600", s)

  def makeHTMLFile(fileName: String, trees: Seq[NodeTree[Judgment]])(implicit opts: PrinterOptions): Unit = {
    val fw = new FileWriter(fileName)
    fw.write("<!DOCTYPE html>")
    fw.write("<html lang=\"en\">")
    fw.write("<head>\n")
    fw.write("<meta charset=\"UTF-8\">\n")
    fw.write("</head>\n\n")
    fw.write("<body>\n")
    fw.write(prettyPrint(trees, 0) + "\n")
    fw.write("</body>\n")
    fw.write("</html>")
    fw.close()
  }
}
