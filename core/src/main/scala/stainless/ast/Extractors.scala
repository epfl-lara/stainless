/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

trait TreeDeconstructor extends inox.ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  def deconstruct(pattern: s.Pattern): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], Seq[s.Pattern], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type], Seq[t.Pattern]) => t.Pattern) = pattern match {
    case s.InstanceOfPattern(binder, ct) =>
      (binder.map(_.toVariable).toSeq, Seq(), Seq(ct), Seq(), (vs, _, tps, _) => {
        t.InstanceOfPattern(vs.headOption.map(_.toVal), tps.head.asInstanceOf[t.ADTType])
      })
    case s.WildcardPattern(binder) =>
      (binder.map(_.toVariable).toSeq, Seq(), Seq(), Seq(), (vs, _, _, _) => {
        t.WildcardPattern(vs.headOption.map(_.toVal))
      })
    case s.ADTPattern(binder, ct, subs) =>
      (binder.map(_.toVariable).toSeq, Seq(), Seq(ct), subs, (vs, _, tps, pats) => {
        t.ADTPattern(vs.headOption.map(_.toVal), tps.head.asInstanceOf[t.ADTType], pats)
      })
    case s.TuplePattern(binder, subs) =>
      (binder.map(_.toVariable).toSeq, Seq(), Seq(), subs, (vs, _, _, pats) => {
        t.TuplePattern(vs.headOption.map(_.toVal), pats)
      })
    case s.LiteralPattern(binder, lit) =>
      (binder.map(_.toVariable).toSeq, Seq(lit), Seq(), Seq(), (vs, es, _, _) => {
        t.LiteralPattern(vs.headOption.map(_.toVal), es.head.asInstanceOf[t.Literal[_]])
      })
    case s.UnapplyPattern(binder, id, tps, subs) =>
      (binder.map(_.toVariable).toSeq, Seq(), tps, subs, (vs, _, tps, pats) => {
        t.UnapplyPattern(vs.headOption.map(_.toVal), id, tps, pats)
      })
  }

  override def deconstruct(expr: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = expr match {
    case s.NoTree(tpe) =>
      (Seq(), Seq(), Seq(tpe), (_, _, tps) => t.NoTree(tps.head))
    case s.Error(tpe, desc) =>
      (Seq(), Seq(), Seq(tpe), (_, _, tps) => t.Error(tps.head, desc))
    case s.Require(pred, body) =>
      (Seq(), Seq(pred, body), Seq(), (_, es, _) => t.Require(es(0), es(1)))
    case s.Ensuring(body, pred) =>
      (Seq(), Seq(body, pred), Seq(), (_, es, _) => t.Ensuring(es(0), es(1).asInstanceOf[t.Lambda]))
    case s.Assert(pred, error, body) =>
      (Seq(), Seq(pred, body), Seq(), (_, es, _) => t.Assert(es(0), error, es(1)))
    case s.Pre(f) =>
      (Seq(), Seq(f), Seq(), (_, es, _) => t.Pre(es.head))

    case s.MatchExpr(scrut, cases) =>

      def rec(p: s.Pattern): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Pattern) = {
        val (vs, es, tps, pats, recons) = deconstruct(p)

        val prec = pats.map(pat => rec(pat))
        (vs ++ prec.flatMap(_._1), es ++ prec.flatMap(_._2), tps ++ prec.flatMap(_._3), (nvs, nes, ntps) => {
          val (outerVs, innerVs) = nvs.splitAt(vs.size)
          val (outerEs, innerEs) = nes.splitAt(es.size)
          val (outerTps, innerTps) = ntps.splitAt(tps.size)

          var rvs = innerVs
          var res = innerEs
          var rtps = innerTps
          val newPats = for ((vs, es, tps, recons) <- prec) yield {
            val (currVs, nextVs) = rvs.splitAt(vs.size)
            rvs = nextVs

            val (currEs, nextEs) = res.splitAt(es.size)
            res = nextEs

            val (currTps, nextTps) = rtps.splitAt(tps.size)
            rtps = nextTps

            recons(currVs, currEs, currTps)
          }

          recons(outerVs, outerEs, outerTps, newPats)
        })
      }

      val recCases = for (caze <- cases) yield {
        val (pvs, pes, ptps, precons) = rec(caze.pattern)
        (caze.optGuard.isDefined, pvs, caze.optGuard.toSeq ++ (caze.rhs +: pes), ptps, precons)
      }

      (recCases.flatMap(_._2), scrut +: recCases.flatMap(_._3), recCases.flatMap(_._4), (vs, es, tps) => {
        val newScrut +: patEs = es

        var rvs = vs
        var res = patEs
        var rtps = tps
        t.MatchExpr(newScrut, for ((hasGuard, vs, es, tps, recons) <- recCases) yield {
          val (currVs, nextVs) = rvs.splitAt(vs.size)
          rvs = nextVs

          val (currEs, nextEs) = res.splitAt(es.size)
          res = nextEs

          val (currTps, nextTps) = rtps.splitAt(tps.size)
          rtps = nextTps

          if (hasGuard) {
            val guard +: rhs +: pes = currEs
            t.MatchCase(recons(currVs, pes, currTps), Some(guard), rhs)
          } else {
            val rhs +: pes = currEs
            t.MatchCase(recons(currVs, pes, currTps), None, rhs)
          }
        })
      })

    case s.FiniteArray(elems, base) =>
      (Seq(), elems, Seq(base), (_, es, tps) => t.FiniteArray(es, tps.head))

    case s.LargeArray(elems, default, size, base) =>
      val (keys, values) = elems.toSeq.unzip
      (Seq(), values :+ default :+ size, Seq(base), {
        case (_, es :+ nd :+ ns, tps) => t.LargeArray((keys zip es).toMap, nd, ns, tps.head)
      })

    case s.ArraySelect(array, index) =>
      (Seq(), Seq(array, index), Seq(), (_, es, _) => t.ArraySelect(es(0), es(1)))

    case s.ArrayUpdated(array, index, value) =>
      (Seq(), Seq(array, index, value), Seq(), (_, es, _) => t.ArrayUpdated(es(0), es(1), es(2)))

    case s.ArrayLength(array) =>
      (Seq(), Seq(array), Seq(), (_, es, _) => t.ArrayLength(es.head))

    case _ => super.deconstruct(expr)
  }

  override def deconstruct(tpe: s.Type): (Seq[s.Type], Seq[s.Flag], (Seq[t.Type], Seq[t.Flag]) => t.Type) = tpe match {
    case s.ArrayType(base) => (Seq(base), Seq(), (tps, _) => t.ArrayType(tps(0)))
    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(f: s.Flag): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Flag) = f match {
    case s.Extern => (Seq(), Seq(), (_, _) => t.Extern)
    case s.Derived(id) => (Seq(), Seq(), (_, _) => t.Derived(id))
    case _ => super.deconstruct(f)
  }
}

trait Extractors extends inox.ast.Extractors { self: Trees =>

  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }

  override val deconstructor: TreeDeconstructor { val s: self.type; val t: self.type } = {
    getDeconstructor(self).asInstanceOf[TreeDeconstructor { val s: self.type; val t: self.type }]
  }

  object PatternExtractor extends {
    protected val s: self.type = self
    protected val t: self.type = self
  } with inox.ast.TreeExtractor {
    type Source = Pattern
    type Target = Pattern

    def unapply(pat: Pattern): Option[(Seq[Pattern], Seq[Pattern] => Pattern)] = {
      val (vs, es, tps, pats, builder) = deconstructor.deconstruct(pat)
      Some(pats, patss => builder(vs, es, tps, patss))
    }
  }

  object FunctionRequires {
    def unapply(f: Forall): Option[(Expr, Expr)] = f match {
      case Forall(args, Implies(Application(pred, args1), Application(Pre(f), args2)))
      if args.map(_.toVariable) == args1 && args2 == args2 =>
        Some((f, pred))

      case _ =>
        None
    }
  }

  object FunctionEnsures {
    def unapply(f: Forall): Option[(Expr, Expr)] = f match {
      case Forall(args, Implies(Application(Pre(f), args1), Application(pred, args2 :+ Application(f2, args3))))
      if args.map(_.toVariable) == args1 && args1 == args2 && args2 == args3 && f == f2 =>
        Some((f, pred))

      case _ =>
        None
    }
  }
}
