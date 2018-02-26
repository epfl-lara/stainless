/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.reflect._
import scala.collection.mutable.{Map => MutableMap}

// Note: we can't extend `ast.Definitions` here as termination.Trees
// extends the bounds on `type Symbols`...
trait Definitions extends imperative.Trees { self: Trees =>

  class ClassDef(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val parents: Seq[ClassType], // Set of direct parents
    val fields: Seq[ValDef],
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

    def children(implicit s: Symbols): Seq[ClassDef] =
      s.classes.values.filter(_.parents.exists(_.id == id)).toSeq

    def descendants(implicit s: Symbols): Seq[ClassDef] =
      children.flatMap(cd => cd +: cd.descendants).distinct

    def methods(implicit s: Symbols): Seq[SymbolIdentifier] = {
      s.functions.values.filter(_.flags contains IsMethodOf(id)).map(_.id.asInstanceOf[SymbolIdentifier]).toSeq
    }

    def typeArgs = tparams map (_.tp)

    def typed(tps: Seq[Type])(implicit s: Symbols): TypedClassDef = TypedClassDef(this, tps)
    def typed(implicit s: Symbols): TypedClassDef = typed(tparams.map(_.tp))

    def copy(
      id: Identifier = this.id,
      tparams: Seq[TypeParameterDef] = this.tparams,
      parents: Seq[ClassType] = this.parents,
      fields: Seq[ValDef] = this.fields,
      flags: Set[Flag] = this.flags
    ): ClassDef = new ClassDef(id, tparams, parents, fields, flags).setPos(this)
  }

  case class TypedClassDef(cd: ClassDef, tps: Seq[Type])(implicit val symbols: Symbols) extends Tree {
    @inline def id: Identifier = cd.id

    private[this] var _typeMap: Map[TypeParameter, Type] = _
    def typeMap: Map[TypeParameter, Type] = {
      if (_typeMap eq null) _typeMap = (cd.typeArgs zip tps).filter(p => p._1 != p._2).toMap
      _typeMap
    }

    private[this] var _parents: Seq[TypedClassDef] = _
    def parents: Seq[TypedClassDef] = {
      if (_parents eq null) _parents = cd.parents.flatMap {
        tpe => typeOps.instantiateType(tpe, typeMap).asInstanceOf[ClassType].lookupClass
      }
      _parents
    }

    private[this] var _ancestors: Seq[TypedClassDef] = _
    def ancestors: Seq[TypedClassDef] = {
      if (_ancestors eq null) _ancestors = cd.ancestors.map {
        tcd => tcd.cd.typed(tcd.tps.map(typeOps.instantiateType(_, typeMap)))
      }
      _ancestors
    }

    private[this] var _children: Seq[TypedClassDef] = _
    def children: Seq[TypedClassDef] = {
      if (_children eq null) _children = cd.children.flatMap { cd =>
        val pct = cd.parents.find(_.id == id).get
        symbols.unify(pct, ClassType(id, tps), cd.typeArgs ++ tps.flatMap(typeOps.typeParamsOf)).map { tpSubst =>
          val bound = tpSubst.map(_._1).toSet
          val fullSubst = tpSubst.toMap ++ cd.typeArgs.filterNot(bound).map(tp => tp -> tp.bounds)
          typeOps.instantiateType(ClassType(cd.id, cd.typeArgs), fullSubst).asInstanceOf[ClassType].tcd
        }
      }
      _children
    }

    private[this] var _descendants: Seq[TypedClassDef] = _
    def descendants: Seq[TypedClassDef] = {
      if (_descendants eq null) _descendants = children.flatMap(tcd => tcd +: tcd.descendants).distinct
      _descendants
    }

    private[this] var _fields: Seq[ValDef] = _
    def fields: Seq[ValDef] = {
      if (_fields eq null) {
        _fields =
          if (typeMap.isEmpty) cd.fields
          else cd.fields.map(vd => vd.copy(tpe = typeOps.instantiateType(vd.tpe, typeMap)))
      }
      _fields
    }

    @inline def toType = ClassType(id, tps)
  }

  case class ClassLookupException(id: Identifier) extends LookupException(id, "class")


  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols
       with TypeOps
       with SymbolOps { self0: Symbols =>

    val classes: Map[Identifier, ClassDef]

    private val typedClassCache: MutableMap[(Identifier, Seq[Type]), Option[TypedClassDef]] = MutableMap.empty
    def lookupClass(id: Identifier): Option[ClassDef] = classes.get(id)
    def lookupClass(id: Identifier, tps: Seq[Type]): Option[TypedClassDef] =
      typedClassCache.getOrElseUpdate(id -> tps, lookupClass(id).map(_.typed(tps)))

    def getClass(id: Identifier): ClassDef = lookupClass(id).getOrElse(throw ClassLookupException(id))
    def getClass(id: Identifier, tps: Seq[Type]): TypedClassDef = lookupClass(id, tps).getOrElse(throw ClassLookupException(id))

    // TODO(nv): remove this and fix the conditionForPattern in oo.SymbolOps
    override protected def ensureWellFormedFunction(fd: FunDef) = {
      typeCheck(fd.fullBody, fd.returnType)
    }

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

    protected class Lookup extends super.Lookup {
      override def get[T <: Definition : ClassTag](name: String): Option[T] = ({
        if (classTag[ClassDef].runtimeClass.isAssignableFrom(classTag[T].runtimeClass)) find(name, classes)
        else super.get[T](name)
      }).asInstanceOf[Option[T]]

      override def apply[T <: Definition : ClassTag](name: String): T = {
        if (classTag[ClassDef].runtimeClass.isAssignableFrom(classTag[T].runtimeClass)) {
          find(name, classes).getOrElse(throw ClassLookupException(FreshIdentifier(name))).asInstanceOf[T]
        } else {
          super.apply[T](name)
        }
      }
    }

    override val lookup = new Lookup
  }

  case object IsInvariant extends Flag("invariant", Seq.empty)
  case object IsAbstract extends Flag("abstract", Seq.empty)
  case object IsSealed extends Flag("sealed", Seq.empty)
  case class IsMethodOf(id: Identifier) extends Flag("method", Seq(id))
  case class Bounds(lo: Type, hi: Type) extends Flag("bounds", Seq(lo, hi))
  case class Variance(variance: Boolean) extends Flag("variance", Seq.empty)

  implicit class TypeParameterWrapper(tp: TypeParameter) {
    def bounds: TypeBounds = {
      tp.flags.collectFirst { case Bounds(lo, hi) => TypeBounds(lo, hi) }
        .getOrElse(TypeBounds(NothingType(), AnyType()))
    }

    def lowerBound: Type = bounds.lo
    def upperBound: Type = bounds.hi

    def isCovariant: Boolean = tp.flags contains Variance(true)
    def isContravariant: Boolean = tp.flags contains Variance(false)
    def isInvariant: Boolean = tp.flags.forall { case Variance(_) => false case _ => true }
  }
}
