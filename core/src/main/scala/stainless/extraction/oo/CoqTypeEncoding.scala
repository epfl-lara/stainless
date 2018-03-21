/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.collection.mutable.{Map => MutableMap}

trait CoqTypeEncoding extends inox.ast.SymbolTransformer { self =>
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
          (cs.isEmpty || cd.fields.isEmpty) &&
          (cs.isEmpty == !(cd.flags contains IsAbstract)) &&
          ((cd.flags contains IsSealed) || cd.methods(syms).isEmpty) &&
          (cd.typeArgs forall (tp => tp.isInvariant && !tp.flags.exists { case Bounds(_, _) => true case _ => false }))
      }

      rootSet
        .filter(isCandidate)
        .flatMap(id => descendants.getOrElse(id, Set.empty) + id)
    }

    val constructors: Map[Identifier, Set[Identifier]] = {
      def rec(id: Identifier): Set[Identifier] = {
        val cs = children.getOrElse(id, Set.empty)
        if (cs.isEmpty) Set(id) else cs.flatMap(rec)
      }

      syms.classes.keys.map(id => id -> rec(id)).toMap
    }

    val constructorId: Map[Identifier, Identifier] = candidates.map { id =>
      val root = roots(id)
      val cids = constructors(root)
      id -> (if (cids == Set(root)) id.freshen else id)
    }.toMap

    object transformer extends oo.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      override def transform(e: s.Expr): t.Expr = e match {
        case s.IsInstanceOf(expr, tpe) => t.BooleanLiteral(true)
        case s.AsInstanceOf(expr,tpe) => transform(expr)
        case _ => super.transform(e)
      }
    }

    val functions: Seq[t.FunDef] = syms.functions.values.toSeq.map(transformer.transform)

    val sorts: Seq[t.ADTSort] = syms.classes.values.toSeq
      .map { sortCd =>
        val sortTparams = sortCd.tparams map transformer.transform
        new t.ADTSort(
          sortCd.id,
          sortTparams,
          constructors(sortCd.id).toSeq.sortBy(_.name).map { cid =>
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
          },
          (sortCd.flags - IsAbstract - IsSealed) map transformer.transform
        ).copiedFrom(sortCd)
      }

    val classes: Seq[t.ClassDef] = syms.classes.values.toList.map(transformer.transform)

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
