/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package xlang

import scala.collection.mutable.{Map => MutableMap}

trait Definitions extends inox.ast.Definitions with ast.Trees { self: Trees =>

  class VarDef(id: Identifier, tpe: Type) extends ValDef(id, tpe) {
    override val flags: Set[Flag] = Set(IsVar)
  }

  object VarDef {
    def apply(id: Identifier, tpe: Type): VarDef = new VarDef(id, tpe)
    def unapply(d: Definition): Option[(Identifier, Type)] = d match {
      case vd: ValDef if vd.flags(IsVar) => Some(vd.id -> vd.tpe)
      case _ => None
    }
  }

  implicit def convertToVar = new VariableConverter[VarDef] {
    def convert(vs: VariableSymbol): VarDef = vs match {
      case vd: VarDef => vd
      case _ => VarDef(vs.id, vs.tpe)
    }
  }

  implicit class VariableSymbolToVar(vs: VariableSymbol) {
    def toVar: VarDef = vs.to[VarDef]
  }

  case class ClassLookupException(id: Identifier) extends LookupException(id, "class")

  case class IsField(isLazy: Boolean) extends Flag("field", Seq(isLazy))
  case object IsInvariant extends Flag("invariant", Seq.empty)
  case object IsAbstract extends Flag("abstract", Seq.empty)
  case object IsVar extends Flag("var", Seq.empty)

  case object Ignore extends Flag("ignore", Seq.empty)
  case object Inline extends Flag("inline", Seq.empty)

  override def extractFlag(name: String, args: Seq[Any]): Flag = (name, args) match {
    case ("stainless.annotation.package$.ignore", Seq()) => Ignore
    case ("stainless.annotation.package$.inline", Seq()) => Inline
    case _ => super.extractFlag(
      if (name.startsWith("stainless.annotation.package$.")) name drop 30 else name,
      args
    )
  }

  class ClassDef(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val parent: Option[Identifier],
    val fields: Seq[ValDef],
    val methods: Seq[Identifier],
    val flags: Set[Flag]
  ) extends Definition {

    def root(implicit s: Symbols): ClassDef = parent.map(id => s.getClass(id).root).getOrElse(this)

    def ancestors(implicit s: Symbols): Seq[ClassDef] = parent.map(id => s.getClass(id)) match {
      case Some(pcd) => pcd +: pcd.ancestors
      case None => Seq.empty
    }

    def typeArgs = tparams map (_.tp)

    def typed(tps: Seq[Type])(implicit s: Symbols): TypedClassDef = TypedClassDef(this, tps)
    def typed(implicit s: Symbols): TypedClassDef = typed(tparams.map(_.tp))
  }

  case class TypedClassDef(cd: ClassDef, tps: Seq[Type])(implicit val symbols: Symbols) extends Tree {
    lazy val id: Identifier = cd.id
    lazy val root: TypedClassDef = cd.root.typed(tps)
    lazy val ancestors: Seq[TypedClassDef] = cd.ancestors.map(_.typed(tps))

    lazy val parent: Option[TypedClassDef] = cd.parent.map(id => symbols.getClass(id, tps))

    lazy val fields: Seq[ValDef] = {
      lazy val tmap = (cd.typeArgs zip tps).toMap
      if (tmap.isEmpty) cd.fields
      else cd.fields.map(vd => vd.copy(tpe = symbols.instantiateType(vd.tpe, tmap)))
    }
    
    def toType = ClassType(id, tps)
  }


  /** $encodingof `import some.package.Path` or `import some.package.path._` */
  case class Import(path: Seq[String], isWildcard: Boolean) extends Tree

  /** Represents a static collection of definitions.
    *
    * @see [[PackageDef]] - corresponds to scala packages
    * @see [[ModuleDef]]  - corresponds to scala objects
    */
  sealed trait DefSet extends Tree

  /** $encodingof `package name; ...` */
  case class PackageDef(id: Identifier, imports: Seq[Import], classes: Seq[Identifier], subs: Seq[DefSet]) extends DefSet

  /** $encodingof `object name { ... }` */
  case class ModuleDef(id: Identifier, imports: Seq[Import], classes: Seq[Identifier], functions: Seq[Identifier], subs: Seq[DefSet]) extends DefSet


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

    override def transform(t: TreeTransformer): Symbols =
      super.transform(t).withClasses(classes.values.toSeq.map(cd => new ClassDef(
        cd.id,
        cd.tparams,
        cd.parent,
        cd.fields.map(t.transform),
        cd.methods,
        cd.flags
      )))

    override def equals(that: Any): Boolean = super.equals(that) && (that match {
      case sym: AbstractSymbols => classes == sym.classes
      case _ => false
    })

    override def hashCode: Int = super.hashCode + 31 * classes.hashCode

    def withClasses(classes: Seq[ClassDef]): Symbols
  }
}

