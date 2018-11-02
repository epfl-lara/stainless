/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.wasm

// A structured document to be printed with nice indentation
abstract class Document {

  def <:>(other: Document) = Lined(Seq(this, other))

  def print: String = {
    val sb = new StringBuffer()

    def rec(d: Document)(implicit ind: Int, first: Boolean): Unit = d match {
      case Raw(s) =>
        if (first && s.nonEmpty) sb append ("  " * ind)
        sb append s
      case Indented(doc) =>
        rec(doc)(ind + 1, first)
      case Lined(Nil, _) => // skip
      case Lined(docs, sep) =>
        rec(docs.head)
        docs.tail foreach { doc =>
          rec(sep)(ind, false)
          rec(doc)(ind, false)
        }
      case Stacked(Nil, _) => // skip
      case Stacked(docs, emptyLines) =>
        rec(docs.head)
        docs.tail foreach { doc =>
          sb append "\n"
          if (emptyLines) sb append "\n"
          rec(doc)(ind, true)
        }
    }

    rec(this)(0, true)
    sb.toString
  }
}
case class Indented(content: Document) extends Document
case class Stacked(docs: Seq[Document], emptyLines: Boolean = false) extends Document
case class Lined(docs: Seq[Document], separator: Document = Raw("")) extends Document
case class Raw(s: String) extends Document

object Stacked {
  def apply(docs: Document*): Stacked = Stacked(docs.toSeq)
}