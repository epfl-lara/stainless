/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.collection.mutable.{Map => MutableMap}

trait Definitions extends ast.Definitions { self: Trees =>

  class ClassDef(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val parents: Seq[ClassType],
    val fields: Seq[ValDef],
    val methods: Seq[SymbolIdentifier],
    val flags: Set[Flag]
  ) extends Definition {

    def ancestors(implicit s: Symbols): Seq[TypedClassDef] = {
      val allAncestors = parents.flatMap(_.lookupClass).flatMap(tcd => tcd +: tcd.ancestors)
      val typedMap = allAncestors.groupBy(_.cd).map { case (cd, tcds) =>
        val tps = cd.typeArgs.zipWithIndex.map { case (tp, i) =>
          val insts @ (head +: tail) = tcds.map(_.tps(i))
          if (tp.isCovariant) s.greatestLowerBound(insts)
          else if (tp.isContravariant) s.leastUpperBound(insts)
          else if (tail.forall(_ == head)) head
          else Untyped
        }

        cd -> cd.typed(tps)
      }
      allAncestors.map(_.cd).distinct.map(typedMap)
    }

    def typeArgs = tparams map (_.tp)

    def typed(tps: Seq[Type])(implicit s: Symbols): TypedClassDef = TypedClassDef(this, tps)
    def typed(implicit s: Symbols): TypedClassDef = typed(tparams.map(_.tp))

    def copy(
      id: Identifier = this.id,
      tparams: Seq[TypeParameterDef] = this.tparams,
      parents: Seq[ClassType] = this.parents,
      fields: Seq[ValDef] = this.fields,
      methods: Seq[SymbolIdentifier] = this.methods,
      flags: Set[Flag] = this.flags
    ): ClassDef = new ClassDef(id, tparams, parents, fields, methods, flags)
  }

  case class TypedClassDef(cd: ClassDef, tps: Seq[Type])(implicit val symbols: Symbols) extends Tree {
    lazy val id: Identifier = cd.id

    private lazy val tpMap: Map[TypeParameter, Type] = (cd.typeArgs zip tps).toMap

    lazy val parents: Seq[TypedClassDef] = cd.parents.flatMap {
      tpe => symbols.instantiateType(tpe, tpMap).asInstanceOf[ClassType].lookupClass
    }

    lazy val ancestors: Seq[TypedClassDef] = cd.ancestors.map {
      tcd => tcd.cd.typed(tcd.tps.map(symbols.instantiateType(_, tpMap)))
    }

    lazy val children: Seq[TypedClassDef] =
      symbols.classes.values
        .filter(_.parents.exists(_.id == id))
        .flatMap { cd =>
          val pct = cd.parents.find(_.id == id).get
          symbols.unify(pct, ClassType(id, tps), cd.typeArgs).map { tpSubst =>
            symbols.instantiateType(ClassType(cd.id, cd.typeArgs), tpSubst.toMap).asInstanceOf[ClassType].tcd
          }
        }.toSeq

    lazy val descendants: Seq[TypedClassDef] = children.flatMap(tcd => tcd +: tcd.descendants)

    lazy val fields: Seq[ValDef] = {
      lazy val tmap = (cd.typeArgs zip tps).toMap
      if (tmap.isEmpty) cd.fields
      else cd.fields.map(vd => vd.copy(tpe = symbols.instantiateType(vd.tpe, tmap)))
    }

    def toType = ClassType(id, tps)
  }

  case class ClassLookupException(id: Identifier) extends LookupException(id, "class")


  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols extends super.AbstractSymbols with TypeOps { self0: Symbols =>
    val classes: Map[Identifier, ClassDef]

    private val typedClassCache: MutableMap[(Identifier, Seq[Type]), Option[TypedClassDef]] = MutableMap.empty
    def lookupClass(id: Identifier): Option[ClassDef] = classes.get(id)
    def lookupClass(id: Identifier, tps: Seq[Type]): Option[TypedClassDef] =
      typedClassCache.getOrElseUpdate(id -> tps, lookupClass(id).map(_.typed(tps)))

    def getClass(id: Identifier): ClassDef = lookupClass(id).getOrElse(throw ClassLookupException(id))
    def getClass(id: Identifier, tps: Seq[Type]): TypedClassDef = lookupClass(id, tps).getOrElse(throw ClassLookupException(id))

    override def asString(implicit opts: PrinterOptions): String = {
      classes.map(p => prettyPrint(p._2, opts)).mkString("\n\n") +
        "\n\n-----------\n\n" +
        super.asString
    }

    override def transform(t: inox.ast.TreeTransformer { val s: self.type }): t.t.Symbols = t.t match {
      case tree: Trees =>
        val tt = t.asInstanceOf[inox.ast.TreeTransformer { val s: self.type; val t: tree.type }]
        SymbolTransformer(tt).transform(this).asInstanceOf[t.t.Symbols]
      case _ => super.transform(t)
    }

    override def equals(that: Any): Boolean = super.equals(that) && (that match {
      case sym: AbstractSymbols => classes == sym.classes
      case _ => false
    })

    override def hashCode: Int = super.hashCode + 31 * classes.hashCode

    def withClasses(classes: Seq[ClassDef]): Symbols
  }

  case object IsInvariant extends Flag("invariant", Seq.empty)
  case object IsAbstract extends Flag("abstract", Seq.empty)
  case object IsMethod extends Flag("method", Seq.empty)
}
