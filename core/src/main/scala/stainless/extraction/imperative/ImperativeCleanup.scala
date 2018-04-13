/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

/** Cleanup the program after running imperative desugaring.
  *
  * This functions simplifies away typical pattern of expressions
  * that can be generated during xlang desugaring phase. The most
  * common case is the generation of function returning tuple with
  * Unit in it, which can be safely eliminated.
  */
trait ImperativeCleanup extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: innerfuns.Trees

  def transform(syms: s.Symbols): t.Symbols = {
    implicit val symbols = syms

    val checkedSyms: t.Symbols = {
      object checker extends {
        val s: self.s.type = self.s
        val t: self.t.type = self.t
      } with CheckingTransformer {
        override def transform(tpe: s.Type): t.Type = tpe match {
          case s.TypeParameter(id, flags) if flags contains s.IsMutable =>
            t.TypeParameter(id, (flags filterNot (_ == s.IsMutable)) map transform).copiedFrom(tpe)
          case _ => super.transform(tpe)
        }

        override def transform(expr: s.Expr): t.Expr = expr match {
          // Desugar Boolean bitwise operations &, | and ^
          case (_: s.BoolBitwiseAnd | _: s.BoolBitwiseOr | _: s.BoolBitwiseXor) =>
            val (lhs, rhs, recons): (s.Expr, s.Expr, (t.Expr, t.Expr) => t.Expr) = expr match {
              case s.BoolBitwiseAnd(lhs, rhs) => (lhs, rhs, t.And(_, _).copiedFrom(expr))
              case s.BoolBitwiseOr(lhs, rhs) => (lhs, rhs, t.Or(_, _).copiedFrom(expr))
              case s.BoolBitwiseXor(lhs, rhs) => (lhs, rhs, (l,r) => t.Not(t.Equals(l, r).copiedFrom(expr)).copiedFrom(expr))
            }

            val l = t.ValDef(FreshIdentifier("lhs"), transform(lhs.getType)).copiedFrom(lhs)
            val r = t.ValDef(FreshIdentifier("rhs"), transform(rhs.getType)).copiedFrom(rhs)
            t.Let(l, transform(lhs),
              t.Let(r, transform(rhs),
                recons(l.toVariable, r.toVariable)).copiedFrom(expr)).copiedFrom(expr)

          case _ => super.transform(expr)
        }

        override def transform(vd: s.ValDef): t.ValDef = {
          val (newId, newTpe) = transform(vd.id, vd.tpe)
          t.ValDef(newId, newTpe, (vd.flags filterNot (_ == s.IsVar)) map transform).copiedFrom(vd)
        }
      }

      t.NoSymbols
        .withSorts(syms.sorts.values.toSeq map checker.transform)
        .withFunctions(syms.functions.values.toSeq map { fd =>
          s.exprOps.preTraversal {
            case o @ s.Old(v: s.Variable) if fd.params exists (_.toVariable == v) =>
              throw MissformedStainlessCode(o, s"Stainless `old` can only occur in postconditions.")
            case o @ s.Old(e) =>
              throw MissformedStainlessCode(o, s"Stainless `old` is only defined on `this` and variables.")
            case _ =>
          } (fd.fullBody)

          checker.transform(fd)
        })
    }

    val pureUnitSyms: t.Symbols = {
      import self.t._
      import checkedSyms._

      object pureUnits extends SelfTreeTransformer {
        override def transform(e: Expr): Expr = e match {
          case tu @ Tuple(es) => Tuple(es.map {
            case IsTyped(e, UnitType()) =>
              val te = transform(e)
              if (isAlwaysPure(te)) UnitLiteral().copiedFrom(te) else te
            case e => transform(e)
          }).copiedFrom(tu)

          case _ => super.transform(e)
        }
      }

      t.NoSymbols
        .withSorts(checkedSyms.sorts.values.toSeq.map(pureUnits.transform))
        .withFunctions(checkedSyms.functions.values.toSeq.map(pureUnits.transform))
    }

    val simpleSyms = t.NoSymbols
      .withSorts(pureUnitSyms.sorts.values.toSeq)
      .withFunctions(pureUnitSyms.functions.values.toSeq.map { fd =>
        fd.copy(fullBody = pureUnitSyms.simplifyLets(fd.fullBody))
      })

    simpleSyms
  }
}

