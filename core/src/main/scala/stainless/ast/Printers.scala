/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

trait Printers extends inox.ast.Printers { self: Trees =>

  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case NoTree(tpe) =>
      p"<empty tree>[$tpe]"

    case Error(tpe, desc) =>
      p"""error[$tpe]("$desc")"""

    case Require(pred, body) =>
      p"""|require($pred)
          |$body"""

    case Assert(pred, Some(err), body) =>
      p"""|assert($pred, "$err")
          |$body"""

    case Assert(pred, None, body) =>
      p"""|assert($pred)
          |$body"""

    case Ensuring(body, post) =>
      p"""|{
          |  $body
          |} ensuring {
          |  $post
          |}"""

    case Pre(f) =>
      p"$f.pre"

    case MatchExpr(s, cases) =>
      optP {
        p"""|$s match {
            |  ${nary(cases, "\n")}
            |}"""
      }

    case MatchCase(pat, optG, rhs) =>
      p"|case $pat "; optG foreach (g => p"if $g "); p"""=>
        |  $rhs"""

    case WildcardPattern(None) => p"_"
    case WildcardPattern(Some(vd)) => p"${vd.toVariable}"

    case ADTPattern(ovd, tpe, pats) =>
      ovd foreach (vd => p"${vd.toVariable} @ ")
      printNameWithPath(tpe.id) // print only the id because we don't want type parameters in patterns
      p"($pats)"

    case InstanceOfPattern(ovd, tpe) =>
      ovd foreach (vd => p"${vd.toVariable} : ")
      p"$tpe"

    case TuplePattern(ovd, subs) =>
      ovd foreach (vd => p"${vd.toVariable} : ")
      p"($subs)"

    case LiteralPattern(ovd, lit) =>
      ovd foreach (vd => p"${vd.toVariable} @ ")
      p"$lit"

    case UnapplyPattern(ovd, id, tps, subs) =>
      ovd foreach (vd => p"${vd.toVariable} @ ")
      printNameWithPath(id)
      p"(${nary(subs)})"

    case ArrayType(base) =>
      p"Array[$base]"

    case FiniteArray(elems, base) =>
      if (elems.isEmpty) {
        p"Array[$base]()"
      } else {
        p"Array($elems)"
      }

    case LargeArray(elems, default, size, base) =>
      if (elems.isEmpty) {
        p"Array($default, ..., $default) (of size $size)"
      } else {
        p"Array(_) (of size $size)"
      }

    case ArraySelect(array, index) =>
      p"$array($index)"

    case ArrayUpdated(array, index, value) =>
      p"$array.updated($index, $value)"

    case ArrayLength(array) =>
      p"$array.length"

    case _ => super.ppBody(tree)
  }

  override protected def isSimpleExpr(e: Expr): Boolean = e match {
    case (_: Assert) | (_: Require) => false
    case _ => super.isSimpleExpr(e)
  }

  override protected def noBracesSub(e: Tree): Seq[Expr] = e match {
    case Assert(_, _, bd) => Seq(bd)
    case Require(_, bd) => Seq(bd)
    case Ensuring(bd, pred) => Seq(bd, pred)
    case MatchCase(_, _, rhs) => Seq(rhs)
    case _ => super.noBracesSub(e)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, Some(_: Ensuring | _: Require | _: Assert | _: MatchExpr | _: MatchCase)) => false
    case (_: Pattern, _) => false
    case _ => super.requiresParentheses(ex, within)
  }

  protected def printNameWithPath(id: Identifier)(implicit ctx: PrinterContext): Unit = {
    p"$id"
  }
}
