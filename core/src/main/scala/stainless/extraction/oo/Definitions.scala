/* Copyright 2009-2018 EPFL, Lausanne */

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
    val flags: Seq[Flag]
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

    def typeArgs = tparams map (_.tp)

    def typed(tps: Seq[Type])(implicit s: Symbols): TypedClassDef = TypedClassDef(this, tps)
    def typed(implicit s: Symbols): TypedClassDef = typed(tparams.map(_.tp))

    def copy(
      id: Identifier = this.id,
      tparams: Seq[TypeParameterDef] = this.tparams,
      parents: Seq[ClassType] = this.parents,
      fields: Seq[ValDef] = this.fields,
      flags: Seq[Flag] = this.flags
    ): ClassDef = new ClassDef(id, tparams, parents, fields, flags).setPos(this)
  }

  case class TypedClassDef(cd: ClassDef, tps: Seq[Type])(implicit val symbols: Symbols) extends Tree {
    copiedFrom(cd)

    @inline def id: Identifier = cd.id

    @inline def tpSubst: Map[TypeParameter, Type] = _tpSubst.get
    private[this] val _tpSubst = inox.utils.Lazy((cd.typeArgs zip tps).filter(p => p._1 != p._2).toMap)

    @inline def parents: Seq[TypedClassDef] = _parents.get
    private[this] val _parents = inox.utils.Lazy(cd.parents.flatMap {
      tpe => typeOps.instantiateType(tpe, tpSubst).asInstanceOf[ClassType].lookupClass
    })

    @inline def ancestors: Seq[TypedClassDef] = _ancestors.get
    private[this] val _ancestors = inox.utils.Lazy(cd.ancestors.map {
      tcd => tcd.cd.typed(tcd.tps.map(typeOps.instantiateType(_, tpSubst)))
    })

    @inline def children: Seq[TypedClassDef] = _children.get
    private[this] val _children = inox.utils.Lazy(cd.children.flatMap { cd =>
      val pct = cd.parents.find(_.id == id).get
      symbols.unify(pct, ClassType(id, tps), cd.typeArgs ++ tps.flatMap(typeOps.typeParamsOf)).map { tpSubst =>
        val bound = tpSubst.map(_._1).toSet
        val fullSubst = tpSubst.toMap ++ cd.typeArgs.filterNot(bound).map(tp => tp -> tp.bounds)
        typeOps.instantiateType(ClassType(cd.id, cd.typeArgs), fullSubst).asInstanceOf[ClassType].tcd
      }
    })

    @inline def descendants: Seq[TypedClassDef] = _descendants.get
    private[this] val _descendants = inox.utils.Lazy(children.flatMap(tcd => tcd +: tcd.descendants).distinct)

    @inline def fields: Seq[ValDef] = _fields.get
    private[this] val _fields = inox.utils.Lazy({
      if (tpSubst.isEmpty) cd.fields
      else cd.fields.map(vd => vd.copy(tpe = typeOps.instantiateType(vd.tpe, tpSubst)))
    })

    @inline def toType = ClassType(id, tps).copiedFrom(this)
  }

  case class ClassLookupException(id: Identifier) extends LookupException(id, "class")


  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols
       with DependencyGraph
       with TypeOps
       with SymbolOps { self0: Symbols =>

    val classes: Map[Identifier, ClassDef]

    private val typedClassCache: MutableMap[(Identifier, Seq[Type]), Option[TypedClassDef]] = MutableMap.empty
    def lookupClass(id: Identifier): Option[ClassDef] = classes.get(id)
    def lookupClass(id: Identifier, tps: Seq[Type]): Option[TypedClassDef] =
      typedClassCache.getOrElse(id -> tps, {
        val res = lookupClass(id).map(_.typed(tps))
        typedClassCache(id -> tps) = res
        res
      })

    def getClass(id: Identifier): ClassDef = lookupClass(id).getOrElse(throw ClassLookupException(id))
    def getClass(id: Identifier, tps: Seq[Type]): TypedClassDef = lookupClass(id, tps).getOrElse(throw ClassLookupException(id))

    override def asString(implicit opts: PrinterOptions): String = {
      classes.map(p => prettyPrint(p._2, opts)).mkString("\n\n") +
        "\n\n-----------\n\n" +
        super.asString
    }

    override def transform(t: inox.transformers.DefinitionTransformer { val s: self.type }): t.t.Symbols =
      t.t match {
        case tree: Trees => SymbolTransformer(
          t.asInstanceOf[inox.transformers.DefinitionTransformer { val s: self.type; val t: tree.type }]
        ).transform(this).asInstanceOf[t.t.Symbols]

        case _ => super.transform(t)
      }

    override protected def ensureWellFormedSymbols: Unit = {
      super.ensureWellFormedSymbols
      for ((_, cd) <- classes) ensureWellFormedClass(cd)
    }

    protected def ensureWellFormedClass(cd: ClassDef): Unit = {
      cd.parents.find(ct => !ct.isTyped(this)).foreach { pcd =>
        throw NotWellFormedException(cd, Some(s"the parent ${pcd.id} of class ${cd.id} is not well typed."))
      }

      cd.parents.find(!_.tcd.cd.flags.contains(IsAbstract)).foreach { pcd =>
        throw NotWellFormedException(cd, 
          Some(s"a concrete class (${pcd.id}) cannot be extended (by ${cd.id}).")
        )
      }
      
      cd.fields.groupBy(_.id).find(_._2.size > 1).foreach { case (id, vds) =>
        throw NotWellFormedException(cd, 
          Some(s"there are at least two fields with the same id ($id) in ${cd.id} (${vds.mkString(",")}).")
        )
      }
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
  case object IsCaseObject extends Flag("caseObject", Seq.empty)
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
