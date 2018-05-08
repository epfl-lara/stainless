/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.collection.mutable.{Map => MutableMap}

trait AdtSpecialization extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: Trees

  def transform(syms: s.Symbols): t.Symbols = {
    import s._

    val children: Map[Identifier, Set[Identifier]] =
      syms.classes.values
        .flatMap(cd => cd.parents.map(_ -> cd))
        .groupBy(_._1.id)
        .mapValues(_.map(_._2.id).toSet)

    val descendants: Map[Identifier, Set[Identifier]] =
      inox.utils.fixpoint { (map: Map[Identifier, Set[Identifier]]) =>
        map.map { case (p, desc) => p -> (desc ++ desc.flatMap(map.getOrElse(_, Set.empty))) }
      } (children)

    val roots: Map[Identifier, Identifier] =
      syms.classes.values
        .flatMap { cd =>
          def root(id: Identifier): Option[Identifier] = {
            val cd = syms.getClass(id)
            cd.parents match {
              case Seq() => Some(id)
              case Seq(ct) if ct.tps == cd.typeArgs => root(ct.id)
              case _ => None
            }
          }
          root(cd.id).map(cd.id -> _)
        }.toMap

    val candidates: Set[Identifier] = {
      val rootSet = roots.values.toSet

      def isCandidate(id: Identifier): Boolean = {
        val cd = syms.getClass(id)
        val cs = children.getOrElse(id, Set.empty)
        (roots contains id) &&
        (cs forall isCandidate) &&
        ((cd.flags contains IsAbstract) || cs.isEmpty) &&
        (!(cd.flags contains IsAbstract) || cd.fields.isEmpty) &&
        (cd.typeArgs forall (tp => tp.isInvariant && !tp.flags.exists { case Bounds(_, _) => true case _ => false }))
      }

      rootSet
        .filter(isCandidate)
        .flatMap(id => descendants.getOrElse(id, Set.empty) + id)
    }

    val extraConstructors: Map[Identifier, Identifier] = {
      def isOpen(id: Identifier): Boolean = {
        val cd = syms.classes(id)
        (cd +: cd.descendants(syms)).exists {
          cd => (cd.flags contains IsAbstract) && !(cd.flags contains IsSealed)
        }
      }

      val openRoots = roots.values.toSet.filter(id => candidates(id) && isOpen(id))
      val openConstructors = openRoots.map(id => id -> FreshIdentifier("Open")).toMap

      candidates.filter(id => isOpen(id)).map(id => id -> openConstructors(roots(id))).toMap
    }

    val constructors: Map[Identifier, Set[Identifier]] = {
      def rec(id: Identifier): Set[Identifier] = {
        (if (syms.classes(id).flags contains IsAbstract) Set() else Set(id)) ++
        children.getOrElse(id, Set.empty).flatMap(rec)
      }

      syms.classes.keys.map(id => id -> (rec(id) ++ extraConstructors.get(id))).toMap
    }

    val constructorId: Map[Identifier, Identifier] = candidates.map { id =>
      val root = roots(id)
      val cids = constructors(root)
      id -> (if (cids == Set(root)) id.freshen else id)
    }.toMap ++ extraConstructors.values.map(id => id -> id)

    object transformer extends oo.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      val caseObjectFunctions: Map[Identifier, t.FunDef] = syms.classes.values
        .filter(cd => candidates(cd.id) && (cd.flags contains IsCaseObject))
        .map(cd => cd.id -> new t.FunDef(
          cd.id.freshen, Seq(), Seq(), transform(cd.typed(syms).toType.setPos(cd)),
          t.ADT(constructorId(cd.id), Seq(), Seq()).setPos(cd), Seq(t.Inline, t.Derived(cd.id))
        ).setPos(cd)).toMap

      override def transform(e: s.Expr): t.Expr = e match {
        case s.ClassSelector(expr, selector) => syms.widen(expr.getType(syms)) match {
          case s.ClassType(id, tps) if candidates(id) =>
            val vd = t.ValDef.fresh("e", t.ADTType(roots(id), tps map transform).copiedFrom(e)).copiedFrom(e)
            t.Let(vd, transform(expr),
              t.Annotated(t.ADTSelector(vd.toVariable, selector).copiedFrom(e), Seq(t.Unchecked)).copiedFrom(e)
            ).copiedFrom(e)
          case _ => super.transform(e)
        }

        case s.ClassConstructor(s.ClassType(id, Seq()), Seq()) if caseObjectFunctions contains id =>
          t.FunctionInvocation(caseObjectFunctions(id).id, Seq(), Seq()).copiedFrom(e)

        case s.ClassConstructor(s.ClassType(id, tps), args) if candidates(id) =>
          t.ADT(constructorId(id), tps map transform, args map transform).copiedFrom(e)

        case s.MatchExpr(scrut, cases) =>
          t.MatchExpr(transform(scrut), cases map { case cse @ s.MatchCase(pat, optGuard, rhs) =>
            var guards: Seq[Expr] = Nil
            val newPat = s.patternOps.postMap {
              case iop @ s.InstanceOfPattern(ob, tpe @ ClassType(id, tps)) if candidates(id) =>
                if (constructors(id) == Set(id)) {
                  val subs = tpe.tcd(syms).fields.map(_ => s.WildcardPattern(None).copiedFrom(pat))
                  Some(s.ADTPattern(ob, constructorId(id), tps, subs).copiedFrom(iop))
                } else if (roots(id) == id) {
                  Some(s.WildcardPattern(ob).copiedFrom(iop))
                } else {
                  val v = ob getOrElse ValDef(
                    FreshIdentifier("v"),
                    s.ADTType(roots(id), tps).copiedFrom(iop)
                  ).copiedFrom(iop)

                  guards :+= s.orJoin(constructors(id).toSeq.sortBy(_.name).map { cid =>
                    s.IsConstructor(v.toVariable, constructorId(cid)).copiedFrom(iop)
                  })
                  Some(s.WildcardPattern(Some(v)).copiedFrom(iop))
                }
              case _ => None
            } (pat)

            val newGuard = (optGuard ++ guards).toSeq match {
              case Nil => None
              case seq => Some(s.andJoin(seq)).filterNot(_ == s.BooleanLiteral(true))
            }

            t.MatchCase(transform(newPat), newGuard map transform, transform(rhs)).copiedFrom(cse)
          }).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(pat: s.Pattern): t.Pattern = pat match {
        case s.ClassPattern(binder, s.ClassType(id, tps), subs) if candidates(id) =>
          t.ADTPattern(binder map transform, constructorId(id), tps map transform, subs map transform).copiedFrom(pat)
        case _ => super.transform(pat)
      }

      override def transform(tpe: s.Type): t.Type = tpe match {
        case s.ClassType(id, tps) if candidates(id) =>
          if (id == roots(id)) {
            t.ADTType(id, tps map transform).copiedFrom(tpe)
          } else {
            val vd = t.ValDef(FreshIdentifier("v"), t.ADTType(roots(id), tps map transform).copiedFrom(tpe)).copiedFrom(tpe)
            t.RefinementType(vd, t.orJoin(constructors(id).toSeq.sortBy(_.name).map { cid =>
              t.IsConstructor(vd.toVariable, constructorId(cid)).copiedFrom(tpe)
            }).copiedFrom(tpe)).copiedFrom(tpe)
          }
        case _ => super.transform(tpe)
      }
    }

    val functions: Seq[t.FunDef] =
      syms.functions.values.toSeq.map(transformer.transform) ++
      transformer.caseObjectFunctions.values

    val sorts: Seq[t.ADTSort] = syms.classes.values.toSeq
      .filter(cd => candidates(cd.id) && cd.parents.isEmpty)
      .map { sortCd =>
        val sortTparams = sortCd.tparams map transformer.transform
        val optOpen = extraConstructors.get(sortCd.id)
        new t.ADTSort(
          sortCd.id,
          sortTparams,
          constructors(sortCd.id).toSeq.sortBy(_.name).map { cid =>
            if (optOpen == Some(cid)) {
              val field = t.ValDef(FreshIdentifier("x"), t.IntegerType().copiedFrom(sortCd)).copiedFrom(sortCd)
              new t.ADTConstructor(cid, sortCd.id, Seq(field)).copiedFrom(sortCd)
            } else {
              val consCd = syms.classes(cid)
              val tpMap = (consCd.tparams.map(tpd => transformer.transform(tpd).tp) zip sortTparams.map(_.tp)).toMap
              new t.ADTConstructor(
                constructorId(cid),
                sortCd.id,
                consCd.fields map { vd =>
                  val tvd = transformer.transform(vd)
                  tvd.copy(tpe = t.typeOps.instantiateType(tvd.tpe, tpMap))
                }
              ).copiedFrom(consCd)
            }
          },
          sortCd.flags filterNot (f => f == IsAbstract || f == IsSealed) map transformer.transform
        ).copiedFrom(sortCd)
      }

    val classes: Seq[t.ClassDef] = syms.classes.values
      .filterNot(cd => candidates(cd.id))
      .map(transformer.transform).toSeq

    val finalSyms = t.NoSymbols.withFunctions(functions).withSorts(sorts).withClasses(classes)

    for (fd <- finalSyms.functions.values) {
      if (!finalSyms.isSubtypeOf(fd.fullBody.getType(finalSyms), fd.returnType)) {
        println(fd)
        println(finalSyms.explainTyping(fd.fullBody)(t.PrinterOptions(printUniqueIds = true, symbols = Some(finalSyms))))
      }
    }

    finalSyms
  }
}
