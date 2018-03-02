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
      } (children).withDefaultValue(Set.empty)

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

      private def isRelated(id1: Identifier, id2: Identifier): Boolean =
        id1 == id2 || descendants(id1)(id2) || descendants(id2)(id1)

      private def withPre(oid: Identifier, id: Identifier, v: t.Variable, body: t.Expr): t.Expr = {
        import t.dsl._
        val cons = constructors(oid).toSeq.sortBy(_.name)
        if (descendants(oid)(id)) t.Require(t.orJoin(cons.map(v is _)), body)
        else body
      }

      private val wrapperCache: MutableMap[(Identifier, Identifier), t.FunDef] = MutableMap.empty
      private def wrapper(oid: Identifier, id: Identifier): Identifier = wrapperCache.getOrElse(oid -> id, {
        import t.dsl._
        val cons = (if (descendants(oid)(id)) constructors(id) else constructors(oid)).toSeq.sortBy(_.name)
        mkFunDef(FreshIdentifier("wrap" + oid.name + "To" + id.name), t.Inline, t.Unchecked)(
          symbols.getClass(oid).tparams.map(_.id.name) : _*
        ) { case tparams =>
          (Seq("x" :: t.ADTType(oid, tparams)), t.ADTType(id, tparams), { case Seq(v) =>
            withPre(oid, id, v, t.MatchExpr(v, cons.map { cid =>
              val consCd = symbols.getClass(cid)
              val tpMap = ((consCd.typeArgs map (transform(_).asInstanceOf[t.TypeParameter])) zip tparams).toMap
              val binders = consCd.fields.map(vd => t.ValDef(vd.id.freshen, t.typeOps.instantiateType(transform(vd.tpe), tpMap)))

              val (cseId, adtId) =
                if (descendants(oid)(id)) (cid, constructorMapping(id)(cid))
                else (constructorMapping(oid)(cid), cid)

              t.MatchCase(
                t.ADTPattern(None, cseId, tparams, binders.map(vd => t.WildcardPattern(Some(vd)))),
                None,
                t.ADT(adtId, tparams, binders.map(_.toVariable)))
            }))
          })
        }
      }).id

      def wrap(e: s.Expr, id: Identifier): t.Expr = {
        val s.ClassType(oid, tps) = e.getType
        assert(isRelated(oid, id))
        if (oid == id) transform(e)
        else t.FunctionInvocation(wrapper(oid, id), tps map transform, Seq(transform(e))).copiedFrom(e)
      }

      def wrap(e: s.Expr): t.Expr = wrap(e, roots(e.getType.asInstanceOf[s.ClassType].id))

      val (option, some, none, optionSort) = symbols.lookup.get[s.ClassDef]("stainless.lang.Option") match {
        case Some(cd) =>
          val some = cd.children.find(_.fields.nonEmpty).get
          val none = cd.children.find(_.fields.isEmpty).get
          (cd.id, some.id, none.id, None)
        case None =>
          val sort = t.dsl.mkSort(ast.SymbolIdentifier("stainless.lang.Option"))("A") {
            case Seq(aT) => Seq(
              (ast.SymbolIdentifier("stainless.lang.Some"), Seq(t.ValDef(FreshIdentifier("value"), aT))),
              (ast.SymbolIdentifier("stainless.lang.None"), Seq())
            )
          }
          val Seq(some, none) = sort.constructors
          (sort.id, some.id, none.id, Some(sort))
      }

      private val unapplierCache: MutableMap[(Identifier, Identifier), t.FunDef] = MutableMap.empty
      private def unapplier(oid: Identifier, id: Identifier): Identifier = unapplierCache.getOrElseUpdate(oid -> id, {
        import t.dsl._
        mkFunDef(FreshIdentifier("unwrap" + oid.name + "To" + id.name), t.Inline, t.Unchecked)(
          symbols.getClass(oid).tparams.map(_.id.name) : _*
        ) { case tparams =>
          (Seq("x" :: t.ADTType(oid, tparams)), T(option)(t.ADTType(id, tparams)), {
            case Seq(v) => withPre(oid, id, v, C(some)(t.ADTType(id, tparams))(
              t.FunctionInvocation(wrapper(oid, id), tparams, Seq(v))
            ))
          })
        }
      }).id

      def unapply(ct: s.ClassType, id: Identifier, sub: t.Pattern): t.Pattern = {
        val s.ClassType(oid, tps) = ct
        if (oid == id) sub
        else t.UnapplyPattern(None, unapplier(oid, id), tps map transform, Seq(sub)).copiedFrom(sub)
      }

      def unapply(ct: s.ClassType, sub: t.Pattern): t.Pattern = unapply(ct, roots(ct.id), sub)

      private case class InfeasiblePattern() extends Exception("Pattern is infeasible")

      private def transformPattern(scrut: s.Expr, pattern: s.Pattern): t.Pattern = {
        def transformSub(inType: s.Type, tpe: s.Type, sub: t.Pattern): t.Pattern = (inType, tpe) match {
          case (ct @ s.ClassType(id1, tps1), s.ClassType(id2, tps2))
          if candidates(id1) && candidates(id2) => 
            if (isRelated(id1, id2)) unapply(ct, id2, sub)
            else throw InfeasiblePattern()
          case (ct @ s.ClassType(id, tps), _) if candidates(id) =>
            unapply(ct, sub)
          case (_, s.ClassType(id, tps)) if candidates(id) =>
            unapply(s.ClassType(roots(id), tps), id, sub)
          case _ => sub
        }

        def rec(inType: s.Type, pattern: s.Pattern): t.Pattern = pattern match {
          case s.WildcardPattern(ob) => t.WildcardPattern(ob map transform).copiedFrom(pattern)

          case s.InstanceOfPattern(ob, tpe) =>
            transformSub(inType, tpe, t.InstanceOfPattern(ob map transform, transform(tpe)))

          case s.ClassPattern(ob, ct @ s.ClassType(id, tps), subs) =>
            val tob = ob map transform
            val ttps = tps map transform
            val tsubs = (symbols.getClass(id, tps).fields zip subs).map { case (vd, sub) => rec(vd.tpe, sub) }

            transformSub(inType, ct,
              if (candidates(id)) t.ADTPattern(tob, inType match {
                case s.ClassType(id2, _) => constructorMapping(id2)(id)
                case _ => constructorMapping(roots(id))(id)
              }, ttps, tsubs).copiedFrom(pattern)
              else t.ClassPattern(tob, transform(ct).asInstanceOf[t.ClassType], tsubs).copiedFrom(pattern))

          case s.TuplePattern(ob, subs) => inType match {
            case s.TupleType(tps) =>
              t.TuplePattern(ob map transform, (tps zip subs) map (rec(_, _)).tupled).copiedFrom(pattern)
            case _ =>
              t.TuplePattern(ob map transform, subs map (rec(s.AnyType(), _))).copiedFrom(pattern)
          }

          case up @ s.UnapplyPattern(ob, id, tps, subs) =>
            val subTps = up.getGet.returnType match {
              case tpe if subs.size == 1 => Seq(tpe)
              case s.TupleType(tps2) => tps2
              case _ => subs.map(_ => AnyType())
            }

            transformSub(inType, symbols.getFunction(id, tps).params.head.tpe,
              t.UnapplyPattern(ob map transform, id, tps map transform,
                (subTps zip subs) map (rec(_, _)).tupled).copiedFrom(pattern))

          case s.LiteralPattern(ob, lit) =>
            t.LiteralPattern(ob map transform, transform(lit).asInstanceOf[t.Literal[_]])
        }

        rec(scrut.getType, pattern)
      }

      private def transformArgs(args: Seq[(s.Expr, s.Type)]): Seq[t.Expr] = args map {
        case (e, tpe) => (e.getType, tpe) match {
          case (s.ClassType(id1, tps1), s.ClassType(id2, tps2))
          if candidates(id1) && candidates(id2) => wrap(e, id2)
          case (s.ClassType(id, tps), _) if candidates(id) => wrap(e)
          case _ => transform(e)
        }
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
            if (isRelated(id1, id2)) wrap(expr, id2)
            else t.Assert(
              t.BooleanLiteral(false).copiedFrom(e),
              Some("Cast error"),
              t.Choose(
                t.ValDef(FreshIdentifier("res"), transform(tpe)).copiedFrom(e),
                t.BooleanLiteral(true).copiedFrom(e)).copiedFrom(e)).copiedFrom(e)
          case (IsTyped(_, s.ClassType(id, tps)), _) if candidates(id) =>
            t.AsInstanceOf(wrap(expr), transform(tpe)).copiedFrom(e)
          case _ => super.transform(e)
        }

        case s.ClassSelector(expr, sel) => expr.getType match {
          case s.ClassType(id, tps) if candidates(id) =>
            t.ADTSelector(transform(expr), fieldMapping(id)(sel)).copiedFrom(e)
          case _ => super.transform(e)
        }

        case s.ClassConstructor(ct @ s.ClassType(id, tps), args) =>
          val targs = transformArgs(args zip symbols.getClass(id, tps).fields.map(_.tpe))
          if (candidates(id)) t.ADT(constructorMapping(roots(id))(id), tps map transform, targs).copiedFrom(e)
          else t.ClassConstructor(transform(ct).asInstanceOf[t.ClassType], targs).copiedFrom(e)

        case s.FunctionInvocation(id, tps, args) =>
          val targs = transformArgs(args zip symbols.getFunction(id, tps).params.map(_.tpe))
          t.FunctionInvocation(id, tps map transform, targs).copiedFrom(e)

        case s.MatchExpr(scrut, cases) =>
          t.MatchExpr(transform(scrut), cases map { case cse @ s.MatchCase(pat, optGuard, rhs) =>
            try {
              t.MatchCase(transformPattern(scrut, pat), optGuard map transform, transform(rhs)).copiedFrom(cse)
            } catch {
              case _: InfeasiblePattern => t.MatchCase(
                t.WildcardPattern(None).copiedFrom(pat),
                Some(t.BooleanLiteral(false).copiedFrom(optGuard getOrElse pat)),
                t.Choose(
                  t.ValDef(FreshIdentifier("res"), transform(rhs.getType)).copiedFrom(rhs),
                  t.BooleanLiteral(true).copiedFrom(rhs)).copiedFrom(rhs)
              ).copiedFrom(cse)
            }
          }).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(tpe: s.Type): t.Type = tpe match {
        case s.ClassType(id, tps) if candidates(id) => t.ADTType(id, tps map transform).copiedFrom(tpe)
        case _ => super.transform(tpe)
      }

      def functions: Seq[t.FunDef] = wrapperCache.values.toSeq ++ unapplierCache.values
    }

    val functions: Seq[t.FunDef] = symbols.functions.values.toSeq.map(transformer.transform)

    val sorts: Seq[t.ADTSort] = symbols.classes.values
      .filter(cd => candidates(cd.id))
      .map { sortCd =>
        val sortTparams = sortCd.tparams map transformer.transform
        new t.ADTSort(
          sortCd.id,
          sortTparams,
          constructors(sortCd.id).toSeq.sortBy(_.name).map { cid =>
            val consCd = symbols.classes(cid)
            val consTparams = consCd.tparams map transformer.transform
            val tpMap = (consTparams.map(_.tp) zip sortTparams.map(_.tp)).toMap
            val inst = new t.typeOps.TypeInstantiator(tpMap)
            new t.ADTConstructor(
              constructorMapping(sortCd.id)(cid),
              sortCd.id,
              consCd.fields map { vd =>
                inst.transform(transformer.transform(vd))
                  .copy(id = fieldMapping(sortCd.id)(vd.id)).copiedFrom(vd)
              }
            ).copiedFrom(consCd)
          },
          (sortCd.flags - IsAbstract - IsSealed) map transformer.transform
        ).copiedFrom(sortCd)
      }.toSeq

    val classes: Seq[t.ClassDef] = symbols.classes.values
      .filterNot(cd => candidates(cd.id))
      .map(transformer.transform).toSeq

    val finalSyms = t.NoSymbols
      .withFunctions(functions ++ transformer.functions)
      .withSorts(sorts)
      .withClasses(classes)

    finalSyms
  }
}
