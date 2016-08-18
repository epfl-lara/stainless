/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

trait TreeDeconstructor extends inox.ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  def deconstruct(pattern: s.Pattern): (Seq[s.Expr], Seq[s.Type], Seq[s.Pattern], (Seq[t.Expr], Seq[t.Type], Seq[t.Pattern]) => t.Pattern) = pattern match {
    case s.InstanceOfPattern(binder, ct) =>
      (Seq(), binder.map(_.tpe).toSeq :+ ct, Seq(), (es, tps, pats) => binder match {
        case Some(vd) => t.InstanceOfPattern(Some(t.ValDef(vd.id, tps(0))), tps(1).asInstanceOf[t.ClassType])
        case None => t.InstanceOfPattern(None, tps(0).asInstanceOf[t.ClassType])
      })
    case s.WildcardPattern(binder) => (
      Seq(), binder.map(_.tpe).toSeq, Seq(),
      (es, tps, pats) => t.WildcardPattern((binder zip tps).map(p => t.ValDef(p._1.id, p._2)).headOption)
    )
    case s.CaseClassPattern(binder, ct, subs) => (
      Seq(), binder.map(_.tpe).toSeq :+ ct, subs, (es, tps, pats) => binder match {
        case Some(vd) => t.CaseClassPattern(Some(t.ValDef(vd.id, tps(0))), tps(1).asInstanceOf[t.ClassType], pats)
        case None => t.CaseClassPattern(None, tps(0).asInstanceOf[t.ClassType], pats)
      })
    case s.TuplePattern(binder, subs) => (
      Seq(), binder.map(_.tpe).toSeq, subs,
      (es, tps, pats) => t.TuplePattern((binder zip tps).map(p => t.ValDef(p._1.id, p._2)).headOption, pats)
    )
    case s.LiteralPattern(binder, lit) => (
      Seq(lit), binder.map(_.tpe).toSeq, Seq(),
      (es, tps, pats) => t.LiteralPattern((binder zip tps).map(p => t.ValDef(p._1.id, p._2)).headOption, es.head.asInstanceOf[t.Literal[_]])
    )
    case s.UnapplyPattern(binder, id, tps, subs) => (
      Seq(), binder.map(_.tpe).toSeq ++ tps, subs, (es, tps, pats) => binder match {
        case Some(vd) => t.UnapplyPattern(Some(t.ValDef(vd.id, tps.head)), id, tps.tail, pats)
        case None => t.UnapplyPattern(None, id, tps, pats)
      })
  }

  override def deconstruct(expr: s.Expr): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Expr) = expr match {
    case s.NoTree(tpe) =>
      (Seq(), Seq(tpe), (es, tps) => t.NoTree(tps.head))
    case s.Error(tpe, desc) =>
      (Seq(), Seq(tpe), (es, tps) => t.Error(tps.head, desc))
    case s.Require(pred, body) =>
      (Seq(pred, body), Seq(), (es, tps) => t.Require(es(0), es(1)))
    case s.Ensuring(body, pred) =>
      (Seq(body, pred), Seq(), (es, tps) => t.Ensuring(es(0), es(1).asInstanceOf[t.Lambda]))
    case s.Assert(pred, error, body) =>
      (Seq(pred, body), Seq(), (es, tps) => t.Assert(es(0), error, es(1)))

    case s.MatchExpr(scrut, cases) =>

      def rec(p: s.Pattern): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Pattern) = {
        val (es, tps, pats, recons) = deconstruct(p)
        
        val prec = pats.map(pat => rec(pat))
        (es ++ prec.flatMap(_._1), tps ++ prec.flatMap(_._2), (nes, ntps) => {
          val (outerEs, innerEs) = nes.splitAt(es.size)
          val (outerTps, innerTps) = ntps.splitAt(tps.size)

          var res = innerEs
          var rtps = innerTps
          val newPats = for ((es, tps, recons) <- prec) yield {
            val (currEs, nextEs) = res.splitAt(es.size)
            res = nextEs

            val (currTps, nextTps) = rtps.splitAt(tps.size)
            rtps = nextTps

            recons(currEs, currTps)
          }

          recons(outerEs, outerTps, newPats)
        })
      }

      val recCases = for (caze <- cases) yield {
        val (pes, ptps, precons) = rec(caze.pattern)
        (caze.optGuard.isDefined, caze.optGuard.toSeq ++ (caze.rhs +: pes), ptps, precons)
      }

      (scrut +: recCases.flatMap(_._2), recCases.flatMap(_._3), (es, tps) => {
        val newScrut +: patEs = es

        var res = patEs
        var rtps = tps
        t.MatchExpr(newScrut, for ((hasGuard, es, tps, recons) <- recCases) yield {
          val (currEs, nextEs) = res.splitAt(es.size)
          res = nextEs

          val (currTps, nextTps) = rtps.splitAt(tps.size)
          rtps = nextTps

          if (hasGuard) {
            val guard +: rhs +: pes = currEs
            t.MatchCase(recons(pes, currTps), Some(guard), rhs)
          } else {
            val rhs +: pes = currEs
            t.MatchCase(recons(pes, currTps), None, rhs)
          }
        })
      })

    case _ => super.deconstruct(expr)
  }
}

trait Extractors extends inox.ast.Extractors { self: Trees =>

  val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
  }

  object PatternExtractor extends {
    protected val s: self.type = self
    protected val t: self.type = self
  } with inox.ast.TreeExtractor {
    type Source = Pattern
    type Target = Pattern

    def unapply(pat: Pattern): Option[(Seq[Pattern], Seq[Pattern] => Pattern)] = {
      val (es, tps, pats, builder) = deconstructor.deconstruct(pat)
      Some(pats, patss => builder(es, tps, patss))
    }
  }

  object Pattern {
    def unapply(pat: Pattern): Option[(Option[ValDef], Seq[Pattern], (Option[ValDef], Seq[Pattern]) => Pattern)] = Some(pat match {
      case InstanceOfPattern(binder, ct) => (binder, Seq(), (b, pats) => InstanceOfPattern(b, ct))
      case WildcardPattern(binder) => (binder, Seq(), (b, pats) => WildcardPattern(b))
      case CaseClassPattern(binder, ct, subs) => (binder, subs, (b, pats) => CaseClassPattern(b, ct, pats))
      case TuplePattern(binder, subs) => (binder, subs, (b, pats) => TuplePattern(b, pats))
      case LiteralPattern(binder, lit) => (binder, Seq(), (b, pats) => LiteralPattern(b, lit))
      case UnapplyPattern(binder, id, tps, subs) => (binder, subs, (b, pats) => UnapplyPattern(b, id, tps, pats))
    })
  }
}
