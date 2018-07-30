/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

trait TreeDeconstructor extends inox.ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  /** Rebuild a pattern from the given set of identifiers, variables, expressions, types and subpatterns */
  protected type PatternBuilder = (Seq[Identifier], Seq[t.Variable], Seq[t.Expr], Seq[t.Type], Seq[t.Pattern]) => t.Pattern

  /** Extracted subtrees from a pattern as well as a "builder" */
  protected type DeconstructedPattern = (Seq[Identifier], Seq[s.Variable], Seq[s.Expr], Seq[s.Type], Seq[s.Pattern], PatternBuilder)

  def deconstruct(pattern: s.Pattern): DeconstructedPattern = pattern match {
    case s.WildcardPattern(binder) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(), Seq(), Seq(), (_, vs, _, _, _) => {
        t.WildcardPattern(vs.headOption.map(_.toVal))
      })
    case s.ADTPattern(binder, id, tps, subs) =>
      (Seq(id), binder.map(_.toVariable).toSeq, Seq(), tps, subs, (ids, vs, _, tps, pats) => {
        t.ADTPattern(vs.headOption.map(_.toVal), ids.head, tps, pats)
      })
    case s.TuplePattern(binder, subs) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(), Seq(), subs, (_, vs, _, _, pats) => {
        t.TuplePattern(vs.headOption.map(_.toVal), pats)
      })
    case s.LiteralPattern(binder, lit) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(lit), Seq(), Seq(), (_, vs, es, _, _) => {
        t.LiteralPattern(vs.headOption.map(_.toVal), es.head.asInstanceOf[t.Literal[_]])
      })
    case s.UnapplyPattern(binder, recs, id, tps, subs) =>
      (Seq(id), binder.map(_.toVariable).toSeq, recs, tps, subs, (ids, vs, es, tps, pats) => {
        t.UnapplyPattern(vs.headOption.map(_.toVal), es, ids.head, tps, pats)
      })
  }

  /** Rebuild a match case from the given set of identifiers, variables, expressions and types */
  protected type CasesBuilder = (Seq[Identifier], Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => Seq[t.MatchCase]

  /** Extracted subtrees from a match case as well as a "builder" */
  protected type DeconstructedCases = (Seq[Identifier], Seq[s.Variable], Seq[s.Expr], Seq[s.Type], CasesBuilder)

  protected def deconstructCases(cases: Seq[s.MatchCase]): DeconstructedCases = {
    def rec(p: s.Pattern): (
      Seq[Identifier], Seq[s.Variable], Seq[s.Expr], Seq[s.Type],
      (Seq[Identifier], Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Pattern
    ) = {
      val (ids, vs, es, tps, pats, recons) = deconstruct(p)
      val prec = pats.map(pat => rec(pat))
      (
        ids ++ prec.flatMap(_._1),
        vs ++ prec.flatMap(_._2),
        es ++ prec.flatMap(_._3),
        tps ++ prec.flatMap(_._4),
        (nids, nvs, nes, ntps) => {
          val (outerIds, innerIds) = nids.splitAt(ids.size)
          val (outerVs, innerVs) = nvs.splitAt(vs.size)
          val (outerEs, innerEs) = nes.splitAt(es.size)
          val (outerTps, innerTps) = ntps.splitAt(tps.size)

          var rids = innerIds
          var rvs = innerVs
          var res = innerEs
          var rtps = innerTps
          val newPats = for ((ids, vs, es, tps, recons) <- prec) yield {
            val (currIds, nextIds) = ids.splitAt(ids.size)
            rids = nextIds

            val (currVs, nextVs) = rvs.splitAt(vs.size)
            rvs = nextVs

            val (currEs, nextEs) = res.splitAt(es.size)
            res = nextEs

            val (currTps, nextTps) = rtps.splitAt(tps.size)
            rtps = nextTps

            recons(currIds, currVs, currEs, currTps)
          }

          recons(outerIds, outerVs, outerEs, outerTps, newPats)
        }
      )
    }

    val recCases = for (caze <- cases) yield {
      val (pids, pvs, pes, ptps, precons) = rec(caze.pattern)
      (caze.optGuard.isDefined, pids, pvs, caze.optGuard.toSeq ++ (caze.rhs +: pes), ptps, precons)
    }

    (
      recCases.flatMap(_._2),
      recCases.flatMap(_._3),
      recCases.flatMap(_._4),
      recCases.flatMap(_._5),
      (ids, vs, es, tps) => {
        var rids = ids
        var rvs = vs
        var res = es
        var rtps = tps
        for ((hasGuard, ids, vs, es, tps, recons) <- recCases) yield {
          var (currIds, nextIds) = rids.splitAt(ids.size)
          rids = nextIds

          val (currVs, nextVs) = rvs.splitAt(vs.size)
          rvs = nextVs

          val (currEs, nextEs) = res.splitAt(es.size)
          res = nextEs

          val (currTps, nextTps) = rtps.splitAt(tps.size)
          rtps = nextTps

          if (hasGuard) {
            val guard +: rhs +: pes = currEs
            t.MatchCase(recons(currIds, currVs, pes, currTps), Some(guard), rhs)
          } else {
            val rhs +: pes = currEs
            t.MatchCase(recons(currIds, currVs, pes, currTps), None, rhs)
          }
        }
      }
    )
  }

  override def deconstruct(expr: s.Expr): Deconstructed[t.Expr] = expr match {
    case s.NoTree(tpe) =>
      (Seq(), Seq(), Seq(), Seq(tpe), Seq(), (_, _, _, tps, _) => t.NoTree(tps.head))
    case s.Error(tpe, desc) =>
      (Seq(), Seq(), Seq(), Seq(tpe), Seq(), (_, _, _, tps, _) => t.Error(tps.head, desc))
    case s.Require(pred, body) =>
      (Seq(), Seq(), Seq(pred, body), Seq(), Seq(), (_, _, es, _, _) => t.Require(es(0), es(1)))
    case s.Ensuring(body, pred) =>
      (Seq(), Seq(), Seq(body, pred), Seq(), Seq(), (_, _, es, _, _) => t.Ensuring(es(0), es(1).asInstanceOf[t.Lambda]))
    case s.Assert(pred, error, body) =>
      (Seq(), Seq(), Seq(pred, body), Seq(), Seq(), (_, _, es, _, _) => t.Assert(es(0), error, es(1)))
    case s.Annotated(body, flags) =>
      (Seq(), Seq(), Seq(body), Seq(), flags, (_, _, es, _, flags) => {
        t.Annotated(es(0), flags)
      })

    case s.MatchExpr(scrut, cases) =>
      val (cids, cvs, ces, ctps, crecons) = deconstructCases(cases)
      (cids, cvs, scrut +: ces, ctps, Seq(), (ids, vs, es, tps, _) => {
        val newScrut +: nes = es
        t.MatchExpr(newScrut, crecons(ids, vs, nes, tps))
      })

    case s.FiniteArray(elems, base) =>
      (Seq(), Seq(), elems, Seq(base), Seq(), (_, _, es, tps, _) => t.FiniteArray(es, tps.head))

    case s.LargeArray(elems, default, size, base) =>
      val (keys, values) = elems.toSeq.unzip
      (Seq(), Seq(), values :+ default :+ size, Seq(base), Seq(), {
        case (_, _, es :+ nd :+ ns, tps, _) => t.LargeArray((keys zip es).toMap, nd, ns, tps.head)
      })

    case s.ArraySelect(array, index) =>
      (Seq(), Seq(), Seq(array, index), Seq(), Seq(), (_, _, es, _, _) => t.ArraySelect(es(0), es(1)))

    case s.ArrayUpdated(array, index, value) =>
      (Seq(), Seq(), Seq(array, index, value), Seq(), Seq(), (_, _, es, _, _) => t.ArrayUpdated(es(0), es(1), es(2)))

    case s.ArrayLength(array) =>
      (Seq(), Seq(), Seq(array), Seq(), Seq(), (_, _, es, _, _) => t.ArrayLength(es.head))

    case _ => super.deconstruct(expr)
  }

  override def deconstruct(tpe: s.Type): Deconstructed[t.Type] = tpe match {
    case s.ArrayType(base) => (Seq(), Seq(), Seq(), Seq(base), Seq(), (_, _, _, tps, _) => t.ArrayType(tps(0)))
    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.Ghost => (Seq(), Seq(), Seq(), (_, _, _) => t.Ghost)
    case s.Extern => (Seq(), Seq(), Seq(), (_, _, _) => t.Extern)
    case s.Opaque => (Seq(), Seq(), Seq(), (_, _, _) => t.Opaque)
    case s.Private => (Seq(), Seq(), Seq(), (_, _, _) => t.Private)
    case s.Unchecked => (Seq(), Seq(), Seq(), (_, _, _) => t.Unchecked)
    case s.Synthetic => (Seq(), Seq(), Seq(), (_, _, _) => t.Synthetic)
    case s.Derived(id) => (Seq(id), Seq(), Seq(), (ids, _, _) => t.Derived(ids.head))
    case s.IsField(isLazy) => (Seq(), Seq(), Seq(), (_, _, _) => t.IsField(isLazy))
    case s.IsUnapply(isEmpty, get) => (Seq(isEmpty, get), Seq(), Seq(), (ids, _, _) => t.IsUnapply(ids(0), ids(1)))
    case s.PartialEval => (Seq(), Seq(), Seq(), (_, _, _) => t.PartialEval)
    case _ => super.deconstruct(f)
  }
}

trait Extractors extends inox.ast.Extractors { self: Trees =>

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
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
      val (ids, vs, es, tps, pats, builder) = deconstructor.deconstruct(pat)
      Some(pats, patss => builder(ids, vs, es, tps, patss))
    }
  }
}
