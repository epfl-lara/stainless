/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.collection.mutable.{Map => MutableMap}

trait AdtSpecialization extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: Trees

  def transform(syms: s.Symbols): t.Symbols = {
    import s._
    import syms._

    val children: Map[Identifier, Set[Identifier]] =
      syms.classes.values
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

      syms.classes.keys.map(id => id -> rec(id)).toMap
    }

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
        (cs.isEmpty || cd.fields.isEmpty) &&
        (cs.isEmpty == !(cd.flags contains IsAbstract)) &&
        ((cd.flags contains IsSealed) || cd.methods.isEmpty) &&
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
      id => id -> constructors(id).flatMap(cid => syms.getClass(cid).fields.map(vd => vd.id -> vd.id.freshen)).toMap
    }.toMap

    object transformer extends TransformerWithType {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
      val symbols: syms.type = syms

      private def isRelated(id1: Identifier, id2: Identifier): Boolean =
        id1 == id2 || descendants(id1)(id2) || descendants(id2)(id1)

      private val wrapperCache: MutableMap[(Identifier, Identifier), t.FunDef] = MutableMap.empty
      private def wrapper(oid: Identifier, id: Identifier): Identifier = wrapperCache.getOrElseUpdate(oid -> id, {
        import t.dsl._
        val cons = (if (descendants(oid)(id)) constructors(id) else constructors(oid)).toSeq.sortBy(_.name)
        mkFunDef(FreshIdentifier("wrap" + oid.name + "To" + id.name), t.Inline, t.Unchecked)(
          symbols.getClass(oid).tparams.map(_.id.name) : _*
        ) { case tparams =>
          (Seq("x" :: t.ADTType(oid, tparams)), t.ADTType(id, tparams), { case Seq(v) =>
            t.Require(
              t.orJoin(cons.map(cid => v is constructorMapping(oid)(cid))),
              t.MatchExpr(v, cons.map { cid =>
                val consCd = symbols.getClass(cid)
                val tpMap = ((consCd.typeArgs map (transform(_).asInstanceOf[t.TypeParameter])) zip tparams).toMap
                val binders = consCd.fields.map(vd => t.ValDef(vd.id.freshen, t.typeOps.instantiateType(transform(vd.tpe), tpMap)))
                t.MatchCase(
                  t.ADTPattern(None, constructorMapping(oid)(cid), tparams, binders.map(vd => t.WildcardPattern(Some(vd)))),
                  None,
                  t.ADT(constructorMapping(id)(cid), tparams, binders.map(_.toVariable)))
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

      val (option, some, isEmpty, get, optionSort, optionIsEmpty, optionGet) =
        symbols.lookup.get[s.ClassDef]("stainless.lang.Option") match {
          case Some(cd) =>
            val some = cd.children.find(_.fields.nonEmpty).get
            val isEmpty = symbols.lookup[s.FunDef]("stainless.lang.Option.isEmpty")
            val get = symbols.lookup[s.FunDef]("stainless.lang.Option.get")
            (cd.id, constructorMapping(cd.id)(some.id), isEmpty.id, get.id, None, None, None)
          case None =>
            val Seq(option, some, none, isEmpty, get) =
              Seq("Option", "Some", "None", "Option.isEmpty", "Option.get")
                .map(name => ast.SymbolIdentifier("stainless.lang" + name))
            val value = FreshIdentifier("value")
            import t.dsl._
            (option, some, isEmpty, get,
              Some(mkSort(option)("A") { case Seq(aT) => Seq((some, Seq(t.ValDef(value, aT))), (none, Seq())) }),
              Some(mkFunDef(isEmpty, t.Unchecked)("A") {
                case Seq(aT) => (Seq("x" :: T(option)(aT)), t.BooleanType(), { case Seq(v) => v is none })
              }),
              Some(mkFunDef(get, t.Unchecked)("A") {
                case Seq(aT) => (Seq("x" :: T(option)(aT)), aT, {
                  case Seq(v) => t.Require(v is some, v.getField(value))
                })
              }))
        }

      private val unapplierCache: MutableMap[(Identifier, Identifier), t.FunDef] = MutableMap.empty
      private def unapplier(oid: Identifier, id: Identifier): Identifier = unapplierCache.getOrElseUpdate(oid -> id, {
        import t.dsl._
        val cons = (if (descendants(oid)(id)) constructors(id) else constructors(oid)).toSeq.sortBy(_.name)
        mkFunDef(FreshIdentifier("unwrap" + oid.name + "To" + id.name), t.Inline, t.Unchecked, t.IsUnapply(isEmpty, get))(
          symbols.getClass(oid).tparams.map(_.id.name) : _*
        ) { case tparams =>
          (Seq("x" :: t.ADTType(oid, tparams)), T(option)(t.ADTType(id, tparams)), {
            case Seq(v) => t.Require(
              t.orJoin(cons.map(cid => v is constructorMapping(oid)(cid))),
              C(some)(t.ADTType(id, tparams))(t.FunctionInvocation(wrapper(oid, id), tparams, Seq(v))))
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

      private def maybeUnapply(inType: s.Type, outType: s.Type, pat: t.Pattern): t.Pattern =
        (widen(inType), widen(outType)) match {
          case (ct @ s.ClassType(id1, tps1), s.ClassType(id2, tps2))
          if candidates(id1) && candidates(id2) => 
            if (isRelated(id1, id2)) unapply(ct, id2, pat)
            else throw InfeasiblePattern()
          case (ct @ s.ClassType(id, tps), _) if candidates(id) =>
            unapply(ct, pat)
          case (_, s.ClassType(id, tps)) if candidates(id) =>
            unapply(s.ClassType(roots(id), tps), id, pat)
          case _ => pat
        }

      override def transform(pat: s.Pattern, inType: s.Type): t.Pattern = pat match {
        case s.WildcardPattern(ob) => t.WildcardPattern(ob map transform).copiedFrom(pat)

        case s.InstanceOfPattern(ob, tpe) =>
          maybeUnapply(inType, tpe, t.InstanceOfPattern(ob map transform, transform(tpe)).copiedFrom(pat))

        case s.ClassPattern(ob, ct @ s.ClassType(id, tps), subs) =>
          val tob = ob map transform
          val ttps = tps map transform
          val tsubs = (subs zip symbols.getClass(id, tps).fields.map(_.tpe)) map (p => transform(p._1, p._2))

          if (candidates(id)) {
            val cid = widen(inType) match {
              case s.ClassType(id2, _) => constructorMapping(id2)(id)
              case _ => constructorMapping(roots(id))(id)
            }
            t.ADTPattern(tob, cid, ttps, tsubs).copiedFrom(pat)
          } else {
            t.ClassPattern(tob, transform(ct).asInstanceOf[t.ClassType], tsubs).copiedFrom(pat)
          }

        case s.TuplePattern(ob, subs) => widen(inType) match {
          case s.TupleType(tps) =>
            t.TuplePattern(ob map transform, (subs zip tps) map (p => transform(p._1, p._2))).copiedFrom(pat)
          case _ =>
            t.TuplePattern(ob map transform, subs map (transform(_, s.AnyType()))).copiedFrom(pat)
        }

        case up @ s.UnapplyPattern(ob, id, tps, subs) =>
          val subTps = widen(up.getGet.returnType) match {
            case tpe if subs.size == 1 => Seq(tpe)
            case s.TupleType(tps2) => tps2
            case _ => subs.map(_ => AnyType())
          }

          maybeUnapply(inType, symbols.getFunction(id, tps).params.head.tpe,
            t.UnapplyPattern(ob map transform, id, tps map transform,
              (subs zip subTps) map (p => transform(p._1, p._2))).copiedFrom(pat))

        case s.LiteralPattern(ob, lit) =>
          t.LiteralPattern(ob map transform, transform(lit).asInstanceOf[t.Literal[_]])
      }

      private def maybeWrap(expectedType: s.Type, actualType: s.Type, expr: t.Expr): t.Expr =
        (widen(expectedType), widen(actualType)) match {
          case (in, TupleType(tps)) =>
            val tss = tps.indices.map(i => t.TupleSelect(expr, i + 1).copiedFrom(expr))
            val inTps = in match {
              case TupleType(tps) => tps
              case _ => tps.map(_ => s.AnyType())
            }
            val wrapped = (inTps zip tps zip tss).map { case ((tp1, tp2), ts) => maybeWrap(tp1, tp2, ts) }
            if (tss != wrapped) t.Tuple(wrapped).copiedFrom(expr) else expr

          case (s.ClassType(id1, tps1), s.ClassType(id2, tps2))
          if candidates(id1) && candidates(id2) =>
            if (id1 == id2) expr
            else t.FunctionInvocation(wrapper(id2, id1), tps1 map transform, Seq(expr)).copiedFrom(expr)

          case (_, s.ClassType(id, tps)) if candidates(id) =>
            t.FunctionInvocation(wrapper(roots(id), id), tps map transform, Seq(expr)).copiedFrom(expr)

          case _ => expr
        }

      override def transform(e: s.Expr, tpe: s.Type): t.Expr = e match {
        case s.IsInstanceOf(expr, tpe) => (widen(expr.getType), widen(tpe)) match {
          case (s.ClassType(id1, tps1), s.ClassType(id2, tps2))
          if candidates(id1) && candidates(id2) =>
            val texpr = transform(expr, expr.getType)
            val cMap = constructorMapping(id1)
            t.orJoin(constructors(id2).toSeq.sortBy(_.name).map { cid =>
              t.IsConstructor(texpr, cMap(cid)).copiedFrom(e)
            }).copiedFrom(e)
          case (ct @ s.ClassType(id, tps), _) if candidates(id) =>
            t.BooleanLiteral(isSubtypeOf(ct, tpe)).copiedFrom(e)
          case (_, s.ClassType(id, tps)) if candidates(id) =>
            val texpr = transform(expr, expr.getType)
            t.orJoin(constructors(id).toSeq.sortBy(_.name).map { cid =>
              t.IsConstructor(texpr, cid).copiedFrom(e)
            }).copiedFrom(e)
          case _ => super.transform(e, tpe)
        }

        case s.AsInstanceOf(expr, tpe) => (widen(expr.getType), widen(tpe)) match {
          case (s.ClassType(id1, tps1), s.ClassType(id2, tps2))
          if candidates(id1) && candidates(id2) =>
            if (isRelated(id1, id2)) wrap(expr, id2)
            else t.Assert(
              t.BooleanLiteral(false).copiedFrom(e),
              Some("Cast error"),
              t.Choose(
                t.ValDef(FreshIdentifier("res"), transform(tpe)).copiedFrom(e),
                t.BooleanLiteral(true).copiedFrom(e)).copiedFrom(e)).copiedFrom(e)
          case (s.ClassType(id, tps), _) if candidates(id) =>
            t.AsInstanceOf(wrap(expr), transform(tpe)).copiedFrom(e)
          case _ => super.transform(e)
        }

        case cs @ s.ClassSelector(expr, sel) => widen(expr.getType) match {
          case out @ s.ClassType(id, tps) if candidates(id) =>
            maybeWrap(tpe, cs.getType, t.ADTSelector(transform(expr), fieldMapping(id)(sel)).copiedFrom(e))
          case _ => super.transform(e, tpe)
        }

        case fa @ s.FieldAssignment(obj, sel, value) => widen(obj.getType) match {
          case s.ClassType(id, tps) if candidates(id) =>
            maybeWrap(tpe, fa.getType, t.FieldAssignment(
              transform(obj),
              fieldMapping(id)(sel),
              transform(value, fa.getField.get.tpe)
            ).copiedFrom(e))
          case _ => super.transform(e, tpe)
        }

        case s.ClassConstructor(ct @ s.ClassType(id, tps), args) if candidates(id) =>
          val cid = constructorMapping(widen(tpe) match {
            case s.ClassType(id2, tps2) => id2
            case _ => roots(id)
          })(id)

          t.ADT(cid, tps map transform,
            (args zip symbols.getClass(id, tps).fields.map(_.tpe)) map { case (e, tpe) => transform(e, tpe) }
          ).copiedFrom(e)

        case me @ s.MatchExpr(scrut, cases) =>
          t.MatchExpr(transform(scrut), cases map { case cse @ s.MatchCase(pat, optGuard, rhs) =>
            try {
              t.MatchCase(
                transform(pat, scrut.getType),
                optGuard map (transform(_, s.BooleanType())),
                transform(rhs, tpe)
              ).copiedFrom(cse)
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

        case _ => maybeWrap(tpe, e.getType, super.transform(e, tpe))
      }

      override def transform(tpe: s.Type): t.Type = tpe match {
        case s.ClassType(id, tps) if candidates(id) => t.ADTType(id, tps map transform).copiedFrom(tpe)
        case _ => super.transform(tpe)
      }

      def functions: Seq[t.FunDef] =
        wrapperCache.values.toList ++
        unapplierCache.values ++
        optionIsEmpty ++
        optionGet

      def sorts: Seq[t.ADTSort] = optionSort.toList
    }

    val functions: Seq[t.FunDef] = syms.functions.values.toList.map { fd =>
      new t.FunDef(
        transformer.transform(fd.id),
        fd.tparams map transformer.transform,
        fd.params map transformer.transform,
        transformer.transform(fd.returnType),
        transformer.transform(fd.fullBody, fd.returnType),
        fd.flags map transformer.transform
      ).copiedFrom(fd)
    }

    val sorts: Seq[t.ADTSort] = syms.classes.values.toList
      .filter(cd => candidates(cd.id))
      .map { sortCd =>
        val sortTparams = sortCd.tparams map transformer.transform
        new t.ADTSort(
          sortCd.id,
          sortTparams,
          constructors(sortCd.id).toSeq.sortBy(_.name).map { cid =>
            val consCd = syms.classes(cid)
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
      }

    val classes: Seq[t.ClassDef] = syms.classes.values.toList
      .filterNot(cd => candidates(cd.id))
      .map(transformer.transform).toSeq

    val finalSyms = t.NoSymbols
      .withFunctions(functions ++ transformer.functions)
      .withSorts(sorts ++ transformer.sorts)
      .withClasses(classes)

    for (fd <- finalSyms.functions.values) {
      if (!finalSyms.isSubtypeOf(fd.fullBody.getType(finalSyms), fd.returnType)) {
        println(fd)
        println(finalSyms.explainTyping(fd.fullBody)(t.PrinterOptions(printUniqueIds = true, symbols = Some(finalSyms))))
      }
    }

    finalSyms
  }
}
