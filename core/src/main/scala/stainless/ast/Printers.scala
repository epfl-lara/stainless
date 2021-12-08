/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

trait Printer extends inox.ast.Printer {
  protected val trees: Trees
  import trees._

  protected object Operator {
    def unapply(id: Identifier): Option[String] = {
      if (id.name.forall(!_.isLetterOrDigit))
        Some(id.name)
      else
        None
    }
  }

  protected object FunctionOperator {
    def unapply(expr: Expr): Option[(String, Expr, Expr)] = expr match {
      case FunctionInvocation(Operator(name), Nil, Seq(a, b)) => Some((name, a, b))
      case _ => None
    }
  }

  override protected def precedence(ex: Expr): Int = ex match {
    case (FunctionOperator("|", _, _))                                 => 1
    case (FunctionOperator("^", _, _))                                 => 2
    case (FunctionOperator("&", _, _))                                 => 3
    case (FunctionOperator("&&&", _, _))                               => 3
    case (FunctionOperator("<", _, _) | FunctionOperator(">", _, _))   => 4
    case (FunctionOperator("<<", _, _) | FunctionOperator(">>", _, _)) => 4
    case (FunctionOperator("<=", _, _) | FunctionOperator(">=", _, _)) => 4
    case (FunctionOperator("==> ", _, _))                              => 5
    case (FunctionOperator("+", _, _) | FunctionOperator("-", _, _))   => 7
    case (FunctionOperator("*", _, _) | FunctionOperator("/", _, _))   => 8
    case (FunctionOperator("%", _, _))                                 => 8
    case _ => super.precedence(ex)
  }

  override protected def ppBody(tree: Tree)(using ctx: PrinterContext): Unit = tree match {
    case NoTree(tpe) =>
      p"<empty tree>[$tpe]"

    case Error(tpe, desc) =>
      p"""error[$tpe]("$desc")"""

    case FunctionOperator(id, a, b) =>
      optP {
        p"$a $id $b"
      }

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

    case SplitAnd(exprs) => optP {
      p"${nary(exprs, " &&& ")}"
    }

    case Annotated(body, flags) =>
      for (f <- flags) p"@${f.asString(using ctx.opts)} "
      p"$body"

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

    case ADTPattern(ovd, id, tps, pats) =>
      ovd foreach (vd => p"${vd.toVariable} @ ")
      printNameWithPath(id) // print only the id because we don't want type parameters in patterns
      p"($pats)"

    case TuplePattern(ovd, subs) =>
      ovd foreach (vd => p"${vd.toVariable} : ")
      p"($subs)"

    case LiteralPattern(ovd, lit) =>
      ovd foreach (vd => p"${vd.toVariable} @ ")
      p"$lit"

    case UnapplyPattern(ovd, rec, id, tps, subs) =>
      ovd foreach (vd => p"${vd.toVariable} @ ")
      rec.foreach(e => p"$e.")
      printNameWithPath(id)
      p"(${nary(subs)})"

    case Passes(in, out, cases) =>
      optP {
        p"""|($in, $out) passes {
            |  ${nary(cases, "\n")}
            |}"""
      }

    case ArrayType(base) =>
      p"Array[$base]"

    case RecursiveType(id, tps, size) =>
      p"${ADTType(id, tps)}($size)"

    case ValueType(tpe) =>
      p"Top"

    case AnnotatedType(tpe, flags) =>
      p"$tpe"
      for (f <- flags) p" @${f.asString(using ctx.opts)}"

    case SizedADT(id, tps, args, size) =>
      p"$id${nary(tps, ", ", "[", "]")}($size)($args)"

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

    case Decreases(rank, body) =>
      p"""|decreases($rank)
          |$body"""

    case Max(es) =>
      p"""max($es)"""

    case _ => super.ppBody(tree)
  }

  override protected def isSimpleExpr(e: Expr): Boolean = e match {
    case (_: Assert) | (_: Require) => false
    case (_: Decreases) => false
    case _ => super.isSimpleExpr(e)
  }

  override protected def noBracesSub(e: Tree): Seq[Expr] = e match {
    case Assert(_, _, bd) => Seq(bd)
    case Require(_, bd) => Seq(bd)
    case Ensuring(bd, pred) => Seq(bd, pred)
    case Decreases(_, bd) => Seq(bd)
    case MatchCase(_, _, rhs) => Seq(rhs)
    case _ => super.noBracesSub(e)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, Some(_: Ensuring | _: Require | _: Assert | _: MatchExpr | _: MatchCase)) => false
    case (_, Some(_: Decreases)) => false
    case (_: Pattern, _) => false
    case (e1: Expr, Some(e2 @ FunctionOperator(_, _, _))) if precedence(e2) > precedence(e1) => true
    case _ => super.requiresParentheses(ex, within)
  }

  protected def printNameWithPath(id: Identifier)(using PrinterContext): Unit = p"$id"
}

trait ScalaPrinter extends Printer {
  import trees._

  override protected def ppBody(tree: Tree)(using ctx: PrinterContext): Unit = tree match {
    case FractionLiteral(i, j) if j == 1 => p"""Real(BigInt("$i")"""
    case FractionLiteral(i, j)           => p"""Real(BigInt("$i"), BigInt("$j"))"""
    case IntegerLiteral(i)               => p"""BigInt("$i")"""

    case NoTree(tpe) => p"(??? : $tpe)"

    case Error(tpe, desc) =>
      p"""stainless.lang.error[$tpe]("$desc")"""

    case SplitAnd(exprs) => optP {
      p"${nary(exprs, " &&& ")}"
    }

    case Annotated(body, flags) if flags.nonEmpty =>
      p"($body):"
      for (f <- flags) p" @${f.asString(using ctx.opts)} "

    case Not(Equals(l, r)) => optP {
      p"$l != $r"
    }

    case IsConstructor(e, id) => p"$e.isInstanceOf[$id]"

    case fs @ FiniteSet(rs, base) =>
      if (rs.isEmpty)
        p"Set[$base]()"
      else
        p"Set($rs)"

    case fs @ FiniteBag(rs, base) =>
      if (rs.isEmpty)
        p"Bag[$base]()"
      else
        p"Bag(${rs})"

    case Not(expr) => p"!$expr"

    case ElementOfSet(e, s) => p"$s.contains($e)"
    case SubsetOf(l, r) => p"$l.subsetOf($r)"
    case SetAdd(s, e) => p"$s + $e"
    case SetUnion(l, r) => p"$l ++ $r"
    case BagUnion(l, r) => p"$l ++ $r"

    case SetIntersection(l, r) => p"$l & $r"
    case BagIntersection(l, r) => p"$l & $r"


    case _ => super.ppBody(tree)
  }
}
