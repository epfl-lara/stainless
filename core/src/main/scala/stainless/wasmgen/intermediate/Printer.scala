/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.wasmgen.intermediate

trait Printer extends stainless.ast.Printer {
  protected val trees: Trees
  import trees._
  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case bvl: BVLiteral => ppBody(IntegerLiteral(bvl.toBigInt))

    case Record(tpe, fields) => p"new $tpe($fields)"

    case RecordSelector(record, selector) => p"$record.$selector"

    case FunctionPointer(id) => p"$id"

    case CastDown(e, tp) => p"$e.asInstanceOf[$tp]"

    case CastUp(e, tp) => p"$e.asInstanceOf[$tp]"

    case Sequence(Seq(e1, e2)) =>
      p"""|$e1;
          |$e2"""

    case Sequence(more) =>
      p"""|${more.head};
          |"""
      ppBody(Sequence(more.tail))

    case Output(msg) => p"println($msg)"

    case NewArray(length, init) => p"new Array($length){ ${init.getOrElse("")} }"

    case ArraySet(array, index, value) =>
      p"$array($index) = $value"

    case RecordType(id) =>
      p"$id"

    case rs: RecordSort =>
      p"struct ${rs.id} "
      rs.parent foreach { par => p"extends $par " }
      p"${nary(rs.fields, ", ", "(", ")")}"

    case _ => super.ppBody(tree)
  }
}