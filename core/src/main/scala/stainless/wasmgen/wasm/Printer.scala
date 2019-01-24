/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.wasm

import scala.language.implicitConversions
import Expressions._
import Definitions._

// Printer for Wasm modules
object Printer {
  private implicit def s2d(s: String) = Raw(s)

  private def doc(mod: Module): Document = {
    val Module(name, imports, globals, table, data, functions) = mod
    Stacked(
      "(module ",
      Indented(Stacked(imports map doc)),
      Indented(Stacked(globals map doc)),
      Indented(doc(table)),
      Indented(Stacked(data map doc)),
      Indented(Stacked(functions map doc)),
      ")",
      ""
    )
  }

  private def doc(g: Global): Document = {
    val tpe = if (g.isMutable) s"(mut ${g.tpe})" else g.tpe.toString
    s"(global $$${g.name} $tpe " <:> doc(g.init) <:> ")"
  }

  private def doc(data: Data): Document = {
    def formatByte(fb: FormattedByte) = {
      val b = fb.byte
      if (fb.formatted && b >= 0x20 && b != 0x7F && b != '"' && b != '\\') b.toChar.toString
      else "\\%02X" format b
    }
    s"""(data (offset (i32.const ${data.offset})) "${data.bytes.map(formatByte).mkString}" )"""
  }

  private def doc(t: Table): Document = {
    s"(table anyfunc (elem ${t.funs.map("$" + _).mkString(" ")} ))"
  }

  private def doc(imp: Import): Document = {
    val Import(extModule, name, impType) = imp
    val typeDoc: Document = impType match {
      case FunSig(name, args, returnType) =>
        s"(func $$$name ${args.map(arg => s"(param $arg) ").mkString} (result $returnType))"
      case Memory(size) =>
        s"(memory $size)"
    }
    s"""(import "$extModule" "$name" """ <:> typeDoc <:> ")"
  }

  private def doc(fh: FunDef): Document = {
    val FunDef(name, args, returnType, locals, body) = fh
    val exportDoc: Document = s"""(export "$name" (func $$$name))"""
    val paramsDoc: Document =
      Lined(args map { case ValDef(name, tpe) =>
        Raw(s"(param $$$name $tpe) ")
      })
    val resultDoc: Document = s"(result $returnType) "
    val localsDoc: Document =
      Lined(locals map { case ValDef(name, tpe) =>
        Raw(s"(local $$$name $tpe) ")
      })

    Stacked(
      exportDoc,
      s"(func $$$name " <:> paramsDoc <:> resultDoc <:> localsDoc,
      Indented(Stacked(doc(body))),
      ")"
    )
  }


  private def doc(expr: Expr): Document = {
    expr match {
      case Binary(op, lhs, rhs) =>
        Stacked(
          s"(${lhs.getType}.$op",
          Indented(doc(lhs)),
          Indented(doc(rhs)),
          ")"
        )
      case Unary(op, e) =>
        Stacked(
          s"(${e.getType}.$op",
          Indented(doc(e)),
          ")"
        )
      case I32Const(value) => s"(i32.const $value)"
      case I64Const(value) => s"(i64.const $value)"
      case F32Const(value) => s"(f32.const $value)"
      case F64Const(value) => s"(f64.const $value)"
      case If(label, cond, thenn, elze) =>
        Stacked(
          s"(if $$$label (result ${expr.getType})",
          Indented(doc(cond)),
          "(then",
          Indented(doc(thenn)),
          ") (else ",
          Indented(doc(elze)),
          "))"
        )
      case Loop(label, body) =>
        Stacked(
          s"(loop $$$label (result ${expr.getType})",
          Indented(doc(body)),
          ")"
        )
      case Block(label, body) =>
        Stacked(
          s"(block $$$label (result ${expr.getType})",
          Indented(doc(body)),
          ")"
        )
      case Br(label) => s"(br $$$label)"
      case BrIf(label, cond) =>
        Stacked(
          s"(br_if $$$label",
          Indented(doc(cond)),
          ")"
        )
      case BrTable(labels, default, index, body) =>
        Stacked(
          s"(br_table ${(labels :+ default) map ("$" + _ ) mkString " "}",
          Indented(doc(index)),
          Indented(body map doc getOrElse Raw("")),
          ")"
        )
      case Call(name, _, args) =>
        Stacked(
          s"(call $$$name",
          Indented(Stacked(args map doc: _*)),
          ")"
        )
      case CallIndirect(_, fun, args) =>
        Stacked(
          s"(call_indirect (param ${args.map(_.getType).mkString(" ")}) (result ${expr.getType})",
          Indented(Stacked( (args :+ fun) map doc: _*)),
          ")"
        )
      case Load(tpe, truncate, expr) =>
        val ts = truncate match {
          case Some((tpe, sign)) => s"${tpe.bitSize}_$sign"
          case None => ""
        }
        Stacked(
          s"($tpe.load$ts",
          Indented(doc(expr)),
          ")"
        )
      case Store(truncate, address, value) =>
        val ts = truncate.map(_.bitSize.toString).getOrElse("")
        Stacked(
          s"(${value.getType}.store$ts",
          Indented(doc(address)),
          Indented(doc(value)),
          ")"
        )
      case MemorySize =>
        "(memory.size)"
      case MemoryGrow(size) =>
        Stacked(
          "(memory.grow",
          Indented(doc(size)),
          ")"
        )
      case Return(value) =>
        Stacked(
          "(return",
          Indented(doc(value)),
          ")"
        )
      case Unreachable => "unreachable"
      case Drop(expr) =>
        Stacked(
          s"(drop",
          Indented(doc(expr)),
          ")"
        )
      case Nop => "nop"
      case GetLocal(label) => s"(get_local $$$label)"
      case SetLocal(label, value) =>
        Stacked(
          s"(set_local $$$label",
          Indented(doc(value)),
          s")"
        )
      case GetGlobal(label) => s"(get_global $$$label)"
      case SetGlobal(label, value) =>
        Stacked(
          s"(set_global $$$label",
          Indented(doc(value)),
          s")"
        )
      case Extend(to, sign, e) =>
        Stacked(
          s"($to.extend_$sign/${e.getType}",
          Indented(doc(e)),
          ")"
        )
      case Wrap(to, e) =>
        Stacked(
          s"($to.wrap/${e.getType}",
          Indented(doc(e)),
          ")"
        )
      case Truncate(to, sign, e) =>
        Stacked(
          s"($to.trunc_$sign/${e.getType}",
          Indented(doc(e)),
          ")"
        )
      case Sequence(es) =>
        Stacked(es map doc : _*)
    }

  }

  def apply(mod: Module) = doc(mod).print
  def apply(fh: FunDef) = doc(fh).print
  def apply(expr: Expr) = doc(expr).print

}
