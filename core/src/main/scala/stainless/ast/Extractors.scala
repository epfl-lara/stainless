/* Copyright 2009-2016 EPFL, Lausanne */

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
    case s.InstanceOfPattern(binder, ct) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(), Seq(ct), Seq(), (_, vs, _, tps, _) => {
        t.InstanceOfPattern(vs.headOption.map(_.toVal), tps.head)
      })
    case s.WildcardPattern(binder) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(), Seq(), Seq(), (_, vs, _, _, _) => {
        t.WildcardPattern(vs.headOption.map(_.toVal))
      })
    case s.ADTPattern(binder, ct, subs) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(), Seq(ct), subs, (_, vs, _, tps, pats) => {
        t.ADTPattern(vs.headOption.map(_.toVal), tps.head.asInstanceOf[t.ADTType], pats)
      })
    case s.TuplePattern(binder, subs) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(), Seq(), subs, (_, vs, _, _, pats) => {
        t.TuplePattern(vs.headOption.map(_.toVal), pats)
      })
    case s.LiteralPattern(binder, lit) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(lit), Seq(), Seq(), (_, vs, es, _, _) => {
        t.LiteralPattern(vs.headOption.map(_.toVal), es.head.asInstanceOf[t.Literal[_]])
      })
    case s.UnapplyPattern(binder, id, tps, subs) =>
      (Seq(id), binder.map(_.toVariable).toSeq, Seq(), tps, subs, (ids, vs, _, tps, pats) => {
        t.UnapplyPattern(vs.headOption.map(_.toVal), ids.head, tps, pats)
      })
  }

  override def deconstruct(expr: s.Expr): DeconstructedExpr = expr match {
    case s.NoTree(tpe) =>
      (Seq(), Seq(), Seq(), Seq(tpe), (_, _, _, tps) => t.NoTree(tps.head))
    case s.Error(tpe, desc) =>
      (Seq(), Seq(), Seq(), Seq(tpe), (_, _, _, tps) => t.Error(tps.head, desc))
    case s.Require(pred, body) =>
      (Seq(), Seq(), Seq(pred, body), Seq(), (_, _, es, _) => t.Require(es(0), es(1)))
    case s.Ensuring(body, pred) =>
      (Seq(), Seq(), Seq(body, pred), Seq(), (_, _, es, _) => t.Ensuring(es(0), es(1).asInstanceOf[t.Lambda]))
    case s.Assert(pred, error, body) =>
      (Seq(), Seq(), Seq(pred, body), Seq(), (_, _, es, _) => t.Assert(es(0), error, es(1)))
    case s.Annotated(body, flags) =>
      val dflags = flags.map(deconstruct)

      (dflags.flatMap(_._1), Seq(), body +: dflags.flatMap(_._2), dflags.flatMap(_._3), (ids, _, es, tps) => {
        val body +: fexprs = es

        var vids = ids
        var ves = fexprs
        var vtps = tps
        val flags = dflags.map { case (fids, fes, ftps, frecons) =>
          val (currIds, nextIds) = vids.splitAt(fids.size)
          vids = nextIds

          val (currEs, nextEs) = ves.splitAt(fes.size)
          ves = nextEs

          val (currTps, nextTps) = vtps.splitAt(ftps.size)
          vtps = nextTps

          frecons(currIds, currEs, currTps)
        }

        t.Annotated(body, flags)
      })

    case s.MatchExpr(scrut, cases) =>

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
        scrut +: recCases.flatMap(_._4),
        recCases.flatMap(_._5),
        (ids, vs, es, tps) => {
          val newScrut +: patEs = es

          var rids = ids
          var rvs = vs
          var res = patEs
          var rtps = tps
          t.MatchExpr(newScrut, for ((hasGuard, ids, vs, es, tps, recons) <- recCases) yield {
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
          })
        }
      )

    case s.FiniteArray(elems, base) =>
      (Seq(), Seq(), elems, Seq(base), (_, _, es, tps) => t.FiniteArray(es, tps.head))

    case s.LargeArray(elems, default, size, base) =>
      val (keys, values) = elems.toSeq.unzip
      (Seq(), Seq(), values :+ default :+ size, Seq(base), {
        case (_, _, es :+ nd :+ ns, tps) => t.LargeArray((keys zip es).toMap, nd, ns, tps.head)
      })

    case s.ArraySelect(array, index) =>
      (Seq(), Seq(), Seq(array, index), Seq(), (_, _, es, _) => t.ArraySelect(es(0), es(1)))

    case s.ArrayUpdated(array, index, value) =>
      (Seq(), Seq(), Seq(array, index, value), Seq(), (_, _, es, _) => t.ArrayUpdated(es(0), es(1), es(2)))

    case s.ArrayLength(array) =>
      (Seq(), Seq(), Seq(array), Seq(), (_, _, es, _) => t.ArrayLength(es.head))

    case _ => super.deconstruct(expr)
  }

  override def deconstruct(tpe: s.Type): DeconstructedType = tpe match {
    case s.ArrayType(base) => (Seq(), Seq(base), Seq(), (_, tps, _) => t.ArrayType(tps(0)))
    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.Extern => (Seq(), Seq(), Seq(), (_, _, _) => t.Extern)
    case s.Unchecked => (Seq(), Seq(), Seq(), (_, _, _) => t.Unchecked)
    case s.Derived(id) => (Seq(id), Seq(), Seq(), (ids, _, _) => t.Derived(ids.head))
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
