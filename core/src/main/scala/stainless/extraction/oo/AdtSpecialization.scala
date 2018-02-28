/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.collection.mutable.{Map => MutableMap}

trait AdtSpecialization extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    import s._
    import symbols._

    val children: Map[Identifier, Set[Identifier]] =
      symbols.classes.values
        .flatMap(cd => cd.parents.map(_ -> cd))
        .groupBy(_._1.id)
        .mapValues(_.map(_._2.id).toSet)

    val descendants: Map[Identifier, Set[Identifier]] =
      inox.utils.fixpoint { (map: Map[Identifier, Set[Identifier]]) =>
        map.map { case (p, desc) => p -> (desc ++ desc.flatMap(map.getOrElse(_, Set.empty))) }
      } (children)

    val constructors: Map[Identifier, Set[Identifier]] = {
      def rec(id: Identifier): Set[Identifier] = {
        val cs = children.getOrElse(id, Set.empty)
        if (cs.isEmpty) Set(id) else cs.flatMap(rec)
      }

      symbols.classes.keys.map(id => id -> rec(id)).toMap
    }

    val roots: Map[Identifier, Identifier] =
      symbols.classes.values
        .flatMap { cd =>
          def root(id: Identifier): Option[Identifier] = {
            val cd = symbols.getClass(id)
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
        val cd = symbols.getClass(id)
        val cs = children.getOrElse(id, Set.empty)
        (roots contains id) &&
        (cs forall isCandidate) &&
        (cs.isEmpty || cd.fields.isEmpty) &&
        (cs.isEmpty == !(cd.flags contains IsAbstract)) &&
        ((cd.flags contains IsSealed) || cd.methods(symbols).isEmpty) &&
        (cd.typeArgs forall (tp => tp.isInvariant && !tp.flags.exists { case Bounds(_, _) => true case _ => false }))
      }

      rootSet
        .filter(isCandidate)
        .flatMap(id => descendants.getOrElse(id, Set.empty) + id)
    }

    val constructorMapping: Map[Identifier, Map[Identifier, Identifier]] = candidates.map {
      id => id -> constructors(id).map(cid => cid -> cid.freshen).toMap
    }.toMap

    val fieldMapping: Map[Identifier, Map[Identifier, Identifier]] = candidates.map {
      id => id -> constructors(id).flatMap(cid => symbols.getClass(cid).fields.map(vd => vd.id -> vd.id.freshen)).toMap
    }.toMap

    object transformer extends oo.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      private def getBinders(cid: Identifier, tps: Seq[t.Type]): Seq[t.ValDef] = {
        val consCd = symbols.getClass(cid)
        val tpMap = ((consCd.typeArgs map (transform(_).asInstanceOf[t.TypeParameter])) zip tps).toMap
        consCd.fields.map(vd => t.ValDef(vd.id.freshen, t.typeOps.instantiateType(transform(vd.tpe), tpMap)))
      }

      private val wrapperCache: MutableMap[(Identifier, Identifier), t.FunDef] = MutableMap.empty

      def wrap(e: s.Expr, id: Identifier): t.Expr = {
        val s.ClassType(id1, tps1) = e.getType
        if (id1 == id) transform(e) else {
          assert(descendants(id1)(id))
          val wrapper = wrapperCache.getOrElseUpdate(id1 -> id, {
            val cons = constructors(id).toSeq.sortBy(_.name)
            val tparams = symbols.getClass(id1).tparams.map(tp => t.TypeParameter.fresh(tp.id.name))
            val vd = t.ValDef(FreshIdentifier("x"), t.ADTType(id1, tparams))
            new t.FunDef(
              FreshIdentifier("wrap" + id1.name + "To" + id.name),
              tparams.map(t.TypeParameterDef(_)),
              Seq(vd),
              t.ADTType(id, tparams),
              t.Require(
                t.orJoin(cons.map(cid => t.IsConstructor(vd.toVariable, cid))),
                t.MatchExpr(vd.toVariable, cons.map { cid =>
                  val binders = getBinders(cid, tparams)
                  t.MatchCase(
                    t.ADTPattern(None, cid, tparams, binders.map(vd => t.WildcardPattern(Some(vd)))),
                    None,
                    t.ADT(constructorMapping(id1)(cid), tparams, binders.map(_.toVariable)))
                })),
            Set(t.Inline, t.Unchecked))
          })
          t.FunctionInvocation(wrapper.id, tps1 map transform, Seq(transform(e))).copiedFrom(e)
        }
      }

      def wrap(e: s.Expr): t.Expr = wrap(e, roots(e.getType.asInstanceOf[s.ClassType].id))

      private val unwrapperCache: MutableMap[(Identifier, Identifier), t.FunDef] = MutableMap.empty

      def unwrap(e: s.Expr, id: Identifier): t.Expr = {
        val s.ClassType(id1, tps1) = e.getType
        if (id1 == id) transform(e) else {
          assert(descendants(id)(id1))
          val unwrapper = unwrapperCache.getOrElseUpdate(id1 -> id, {
            val tparams = symbols.getClass(id1).tparams.map(tp => t.TypeParameter.fresh(tp.id.name))
            val vd = t.ValDef(FreshIdentifier("x"), t.ADTType(id, tparams))
            new t.FunDef(
              FreshIdentifier("unwrap" + id1.name + "From" + id.name),
              tparams.map(t.TypeParameterDef(_)),
              Seq(vd),
              t.ADTType(id1, tparams),
              t.MatchExpr(vd.toVariable, constructors(id).toSeq.sortBy(_.name).map { cid =>
                val binders = getBinders(cid, tparams)
                t.MatchCase(
                  t.ADTPattern(None, constructorMapping(id1)(cid), tparams, binders.map(vd => t.WildcardPattern(Some(vd)))),
                  None,
                  t.ADT(cid, tparams, binders.map(_.toVariable)))
              }),
              Set(t.Inline, t.Unchecked))
          })
          t.FunctionInvocation(unwrapper.id, tps1 map transform, Seq(transform(e))).copiedFrom(e)
        }
      }

      def unwrap(e: s.Expr): t.Expr = unwrap(e, roots(e.getType.asInstanceOf[s.ClassType].id))

      private def transformArgs(args: Seq[(s.Expr, s.Type)]): Seq[t.Expr] = args map {
        case (e, tpe) => (e.getType, tpe) match {
          case (s.ClassType(id1, tps1), s.ClassType(id2, tps2))
          if candidates(id1) && candidates(id2) =>
            if (descendants(id1)(id2)) wrap(e, id2)
            else if (descendants(id2)(id1)) unwrap(e, id1)
            else t.AsInstanceOf(unwrap(e), transform(tpe)).copiedFrom(e)
          case (s.ClassType(id, tps), _) if candidates(id) => unwrap(e)
          case _ => transform(e)
        }
      }

      private def transformPattern(scrut: s.Expr, pattern: s.Pattern): (t.Pattern, Map[t.Variable, t.Expr], t.Expr) = {
        def rec(in: s.Expr, pattern: s.Pattern): (t.Pattern, Map[t.Variable, t.Expr], t.Expr) = pattern match {
          case s.WildcardPattern(ob) => (
            t.WildcardPattern(ob map transform).copiedFrom(pattern),
            Map(),
            t.BooleanLiteral(true).copiedFrom(pattern)
          )

          case s.InstanceOfPattern(ob, tpe) =>
            if (Seq(in.getType, tpe).exists { case s.ClassType(id, _) => candidates(id) case _ => false }) {
              val v = s.Variable.fresh("v", in.getType).copiedFrom(pattern)
              (
                t.WildcardPattern(Some(transform(v.toVal))).copiedFrom(pattern),
                ob.map(vd => transform(vd).toVariable -> transform(s.AsInstanceOf(v, tpe).copiedFrom(pattern))).toMap,
                transform(s.IsInstanceOf(v, tpe).copiedFrom(pattern))
              )
            } else {
              (
                t.InstanceOfPattern(ob map transform, transform(tpe)).copiedFrom(pattern),
                Map(),
                t.BooleanLiteral(true).copiedFrom(pattern)
              )
            }

          case s.ClassPattern(ob, ct, subs) =>

          case s.TuplePattern(ob, subs) =>

          case up @ s.UnapplyPattern(ob, id, tps, subs) =>

          case s.LiteralPattern(ob, lit) =>
        }

        rec(scrut, pattern)
      }

      override def transform(e: s.Expr): t.Expr = e match {
        case s.IsInstanceOf(expr, tpe) => (expr, tpe) match {
          case (IsTyped(_, s.ClassType(id1, tps1)), s.ClassType(id2, tps2))
          if candidates(id1) && candidates(id2) =>
            val texpr = transform(expr)
            val cMap = constructorMapping(id1)
            t.orJoin(constructors(id2).toSeq.sortBy(_.name).map { cid =>
              t.IsConstructor(texpr, cMap(cid)).copiedFrom(e)
            }).copiedFrom(e)
          case (IsTyped(_, ct @ s.ClassType(id, tps)), _) if candidates(id) =>
            t.BooleanLiteral(isSubtypeOf(ct, tpe)).copiedFrom(e)
          case (_, s.ClassType(id, tps)) if candidates(id) =>
            val texpr = transform(expr)
            t.orJoin(constructors(id).toSeq.sortBy(_.name).map { cid =>
              t.IsConstructor(texpr, cid).copiedFrom(e)
            }).copiedFrom(e)
          case _ => super.transform(e)
        }

        case s.AsInstanceOf(expr, tpe) => (expr, tpe) match {
          case (IsTyped(_, s.ClassType(id1, tps1)), s.ClassType(id2, tps2))
          if candidates(id1) && candidates(id2) =>
            if (descendants(id1)(id2)) unwrap(expr, id1)
            else if (descendants(id2)(id1)) wrap(expr, id2)
            else t.AsInstanceOf(unwrap(expr), transform(tpe)).copiedFrom(e)
          case (IsTyped(_, s.ClassType(id, tps)), _) if candidates(id) =>
            t.AsInstanceOf(unwrap(expr), transform(tpe)).copiedFrom(e)
          case _ => super.transform(e)
        }

        case s.ClassConstructor(ct @ s.ClassType(id, tps), args) =>
          val targs = transformArgs(args zip symbols.getClass(id, tps).fields.map(_.tpe))
          if (candidates(id)) t.ADT(id, tps map transform, targs).copiedFrom(e)
          else t.ClassConstructor(transform(ct).asInstanceOf[t.ClassType], targs).copiedFrom(e)

        case s.FunctionInvocation(id, tps, args) =>
          val targs = transformArgs(args zip symbols.getFunction(id, tps).params.map(_.tpe))
          t.FunctionInvocation(id, tps map transform, targs)

        case s.MatchExpr(scrut, cases) =>
          t.MatchExpr(transform(scrut), cases map { case cse @ s.MatchCase(pat, optGuard, rhs) =>
            var guards: Seq[Expr] = Nil
            val newPat = s.patternOps.postMap {
              case iop @ s.InstanceOfPattern(ob, tpe @ ClassType(id, tps)) if candidates(id) =>
                if (classToConstructors(id) == Set(id)) {
                  val subs = tpe.tcd(symbols).fields.map(_ => s.WildcardPattern(None).copiedFrom(pat))
                  Some(s.ADTPattern(ob, id, tps, subs).copiedFrom(iop))
                } else {
                  val tpe = s.ADTType(classToParent(id), tps).copiedFrom(iop)
                  val nob = if (classToParent(id) != id) {
                    val v = ob getOrElse ValDef(FreshIdentifier("v"), tpe).copiedFrom(iop)
                    guards :+= orJoin(
                      classToConstructors(id).toSeq.sortBy(_.name)
                        .map(cid => s.IsConstructor(v.toVariable, cid).copiedFrom(iop)))
                    Some(v)
                  } else {
                    ob
                  }

                  // We keep the InstanceOfPattern here so that TypeEncoding can perform the
                  // right instanceOf checks when lub(scrut.getType, tpe) is object.
                  Some(s.InstanceOfPattern(nob, tpe).copiedFrom(iop))
                }
              case _ => None
            } (pat)

            val newGuard = (optGuard ++ guards).toSeq match {
              case Nil => None
              case seq => Some(s.andJoin(seq)).filterNot(_ == s.BooleanLiteral(true))
            }

            t.MatchCase(transform(newPat), newGuard map transform, transform(rhs))
          }).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(pat: s.Pattern): t.Pattern = pat match {
        case s.ClassPattern(binder, s.ClassType(id, tps), subs) if candidates(id) =>
          t.ADTPattern(binder map transform, id, tps map transform, subs map transform).copiedFrom(pat)
        case _ => super.transform(pat)
      }

      override def transform(tpe: s.Type): t.Type = tpe match {
        case s.ClassType(id, tps) if candidates(id) => t.ADTType(id, tps map transform)
        case _ => super.transform(tpe)
      }
    }

    val functions: Seq[t.FunDef] = symbols.functions.values.map { fd =>
      val newParams = fd.params.map(transformer.transform)

      // TODO!
      val tpePres = (fd.params zip newParams).flatMap {
        case (ovd, vd) => ovd.tpe match {
          case s.ClassType(id, tps) if candidates(id) && approximate(id) != id =>
            val ttps = tps map transformer.transform
            Some(t.orJoin(classToConstructors(id).toSeq.sortBy(_.name).map {
              id => t.IsInstanceOf(vd.toVariable, t.ADTType(id, ttps))
            }))
          case _ => None
        }
      }

      val pre = t.andJoin(tpePres ++ fd.precondition(symbols).map(transformer.transform))
      val optPre = if (pre == t.BooleanLiteral(true)) None else Some(pre)

      new t.FunDef(
        fd.id,
        fd.tparams.map(transformer.transform),
        fd.params.map(transformer.transform),
        transformer.transform(fd.returnType),
        t.exprOps.withPrecondition(transformer.transform(fd.fullBody), optPre),
        fd.flags.map(transformer.transform)
      ).setPos(fd)
    }.toSeq

    val sorts: Seq[t.ADTSort] = symbols.classes.values
      .filter(cd => candidates(cd.id) && cd.parents.isEmpty)
      .map { sortCd =>
        val sortTparams = sortCd.tparams map transformer.transform
        val constructors = classToConstructors(sortCd.id).toSeq.sortBy(_.name)

        val adtCons = if (constructors.nonEmpty) {
          constructors.map { cid =>
            val consCd = symbols.classes(cid)
            val consTparams = consCd.tparams map transformer.transform
            val tpMap = (consTparams.map(_.tp) zip sortTparams.map(_.tp)).toMap
            val inst = new t.typeOps.TypeInstantiator(tpMap)
            new t.ADTConstructor(
              cid,
              sortCd.id,
              consCd.fields map (vd => inst.transform(transformer.transform(vd)))
            ).copiedFrom(consCd)
          }
        } else if (!(sortCd.flags contains IsAbstract)) {
          // If this class corresponds to a single concrete class (no abstract class parent)
          Seq(new t.ADTConstructor(
            sortCd.id.freshen,
            sortCd.id,
            sortCd.fields map transformer.transform
          ).copiedFrom(sortCd))
        } else {
          // If this class is a child-less abstract class, we represent it as a class with
          // infinite children (like an uninterpreted sort).
          Seq(new t.ADTConstructor(
            FreshIdentifier(sortCd.id.name + "Cons"),
            sortCd.id,
            Seq(t.ValDef(FreshIdentifier("x"), t.IntegerType()).copiedFrom(sortCd))
          ))
        }

        new t.ADTSort(
          sortCd.id,
          sortTparams,
          adtCons,
          (sortCd.flags - IsAbstract - IsSealed) map transformer.transform
        ).copiedFrom(sortCd)
      }.toSeq

    val classes: Seq[t.ClassDef] = symbols.classes.values
      .filterNot(cd => candidates(cd.id))
      .map(transformer.transform).toSeq

    val finalSyms = t.NoSymbols.withFunctions(functions).withSorts(sorts).withClasses(classes)

    finalSyms
  }
}
