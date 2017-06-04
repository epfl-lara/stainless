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

    val children: Map[Identifier, Set[Identifier]] =
      symbols.classes.values
        .flatMap(cd => cd.parents.map(_ -> cd))
        .groupBy(_._1.id)
        .mapValues(_.map(_._2.id).toSet)

    val descendants: Map[Identifier, Set[Identifier]] =
      inox.utils.fixpoint { (map: Map[Identifier, Set[Identifier]]) =>
        map.map { case (p, desc) => p -> (desc ++ desc.flatMap(map.getOrElse(_, Set.empty))) }
      } (children)

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

    val classToParent: Map[Identifier, Identifier] =
      candidates.map(id => id -> roots(id)).toMap

    val classToConstructors: Map[Identifier, Set[Identifier]] = {
      def rec(id: Identifier): Set[Identifier] = {
        val cs = children.getOrElse(id, Set.empty)
        if (cs.isEmpty) Set(id) else cs.flatMap(rec)
      }

      candidates.map(id => id -> rec(id)).toMap
    }

    def approximate(id: Identifier) = if (classToConstructors(id) == Set(id)) id else classToParent(id)

    object transformer extends oo.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      override def transform(e: s.Expr): t.Expr = e match {
        case s.IsInstanceOf(e, s.ClassType(id, tps)) if candidates(id) =>
          val te = transform(e)
          val ttps = tps map transform
          t.orJoin(classToConstructors(id).toSeq.map {
            id => t.IsInstanceOf(te, t.ADTType(id, ttps)).setPos(e)
          })

        case s.ClassSelector(e, selector) => e.getType(symbols) match {
          case s.ClassType(id, tps) if candidates(id) => t.ADTSelector(transform(e), selector).copiedFrom(e)
          case _ => super.transform(e)
        }

        case s.ClassConstructor(s.ClassType(id, tps), args) if candidates(id) =>
          t.ADT(t.ADTType(id, tps map transform), args map transform).copiedFrom(e)

        case s.MatchExpr(scrut, cases) =>
          super.transform(s.MatchExpr(scrut, for (cse <- cases) yield {
            var binders: Seq[ValDef] = Seq.empty
            val newPattern = s.patternOps.postMap {
              case s.InstanceOfPattern(b, tpe @ s.ClassType(id, _)) if candidates(id) && approximate(id) != id =>
                val ob = b.getOrElse(s.ValDef(FreshIdentifier("x", true), tpe))
                binders :+= ob
                Some(s.WildcardPattern(b))
              case _ => None
            } (cse.pattern)

            val bindGuards = binders.map(vd => s.IsInstanceOf(vd.toVariable, vd.tpe))
            val newGuard = s.andJoin(cse.optGuard.toSeq ++ bindGuards) match {
              case s.BooleanLiteral(true) => None
              case cond => Some(cond)
            }

            val subst = binders.map(vd => vd.toVariable -> s.AsInstanceOf(vd.toVariable, vd.tpe)).toMap
            val newRhs = s.exprOps.replaceFromSymbols(subst, cse.rhs)

            s.MatchCase(newPattern, newGuard, newRhs)
          }).copiedFrom(e))

        case _ => super.transform(e)
      }

      override def transform(pat: s.Pattern): t.Pattern = pat match {
        case s.ClassPattern(binder, s.ClassType(id, tps), subs) if candidates(id) =>
          t.ADTPattern(binder map transform, t.ADTType(id, tps map transform), subs map transform).copiedFrom(pat)
        case _ => super.transform(pat)
      }

      override def transform(tpe: s.Type): t.Type = tpe match {
        case s.ClassType(id, tps) if candidates(id) => t.ADTType(approximate(id), tps map transform)
        case _ => super.transform(tpe)
      }
    }

    val functions: Seq[t.FunDef] = symbols.functions.values.map { fd =>
      val newParams = fd.params.map(transformer.transform)
      val tpePres = (fd.params zip newParams).flatMap {
        case (ovd, vd) => ovd.tpe match {
          case s.ClassType(id, tps) if candidates(id) && approximate(id) != id =>
            val ttps = tps map transformer.transform
            Some(t.orJoin(classToConstructors(id).toSeq.map {
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
      ).setPos(fd.getPos)
    }.toSeq

    val sortClasses = symbols.classes.values.filter { cd =>
      candidates(cd.id) &&
      cd.parents.isEmpty &&
      children.getOrElse(cd.id, Set.empty).nonEmpty
    }

    val sorts: Seq[t.ADTSort] = sortClasses.map(cd => new t.ADTSort(
      cd.id,
      cd.tparams map transformer.transform,
      classToConstructors(cd.id).toSeq,
      (cd.flags - IsAbstract - IsSealed) map transformer.transform
    ).copiedFrom(cd)).toSeq

    val consClasses = symbols.classes.values.filter { cd =>
      candidates(cd.id) &&
      children.getOrElse(cd.id, Set.empty).isEmpty
    }

    val cons: Seq[t.ADTConstructor] = consClasses.map(cd => new t.ADTConstructor(
      cd.id,
      cd.tparams map transformer.transform,
      if (classToParent(cd.id) == cd.id) None else Some(classToParent(cd.id)),
      cd.fields map transformer.transform,
      (cd.flags - IsSealed) map transformer.transform
    ).copiedFrom(cd)).toSeq

    val classes: Seq[t.ClassDef] = symbols.classes.values
      .filterNot(cd => candidates(cd.id))
      .map(transformer.transform).toSeq

    t.NoSymbols.withFunctions(functions).withADTs(sorts ++ cons).withClasses(classes)
  }
}
