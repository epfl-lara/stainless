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
        def isImperativeFlag(f: s.Flag): Boolean = f.name match {
          case "pure" | "var" | "mutable" => true
          case _ => false
        }

        override def transform(tpe: s.Type): t.Type = tpe match {
          case s.TypeParameter(id, flags) if flags contains s.IsMutable =>
            t.TypeParameter(id, (flags filterNot isImperativeFlag) map transform).copiedFrom(tpe)
          case _ => super.transform(tpe)
        }

        def transformFunction(fd: s.FunDef): t.FunDef = {
          transform(fd.copy(flags = fd.flags filterNot isImperativeFlag))
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

          case s.Variable(id, tpe, flags) =>
            t.Variable(id, transform(tpe), flags filterNot isImperativeFlag map transform)

          case s.LetRec(defs, body) =>
            val newDefs = defs map { case s.LocalFunDef(name, tparams, body) =>
              t.LocalFunDef(transform(name), tparams.map(transform), transform(body).asInstanceOf[t.Lambda])
            }
            t.LetRec(newDefs, transform(body))

          // Cleanup leftover `old` nodes if they were used on a reference which is not actually mutated.
          case s.Old(e) => transform(e)

          case _ => super.transform(expr)
        }

        override def transform(vd: s.ValDef): t.ValDef = {
          val (newId, newTpe) = transform(vd.id, vd.tpe)
          t.ValDef(newId, newTpe, (vd.flags filterNot isImperativeFlag) map transform).copiedFrom(vd)
        }
      }

      t.NoSymbols
        .withSorts(syms.sorts.values.toSeq map checker.transform)
        .withFunctions(syms.functions.values.toSeq map checker.transformFunction)
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

