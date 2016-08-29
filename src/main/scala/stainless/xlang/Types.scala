/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package xlang

import scala.collection.mutable.{Map => MutableMap}

trait Types extends inox.ast.Types with inox.ast.Definitions with ast.Trees { self: Trees =>

  class VarDef(id: Identifier, tpe: Type) extends ValDef(id, tpe) {
    override val flags: Set[Annotation] = Set(IsVar)
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

  class ClassType(id: Identifier, tps: Seq[Type]) extends ADTType(id, tps) {
    def lookupClass(implicit s: Symbols): Option[TypedClassDef] = s.lookupClass(id, tps)
    def tcd(implicit s: Symbols): TypedClassDef = s.getClass(id, tps)

    private[xlang] def getField(selector: Identifier)(implicit s: Symbols): Option[ValDef] = {
      def rec(tcd: TypedClassDef): Option[ValDef] =
        tcd.fields.collectFirst { case vd @ ValDef(`selector`, _) => vd }.orElse(tcd.parent.flatMap(rec))
      lookupClass.flatMap(rec)
    }
  }

  object ClassType {
    def apply(id: Identifier, tps: Seq[Type]): ClassType = new ClassType(id, tps)
    def unapply(tpe: Type): Option[(Identifier, Seq[Type])] = tpe match {
      case ct: ClassType => Some((ct.id, ct.tps))
      case _ => None
    }
  }

  case class ClassLookupException(id: Identifier) extends LookupException(id, "class")

  case object IsInvariant extends Annotation("__$invariant", Seq.empty)
  case object IsAbstract extends Annotation("__$abstract", Seq.empty)
  case object IsInlined extends Annotation("__$inline", Seq.empty)
  case object IsVar extends Annotation("__$var", Seq.empty)

  case class IsField(isLazy: Boolean) extends Annotation("__$field", Seq(Some(isLazy)))
  case object Ignore extends Annotation("ignore", Seq.empty)

  class ClassDef(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val parent: Option[Identifier],
    val fields: Seq[ValDef],
    val methods: Seq[Identifier],
    val flags: Set[Annotation]
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
      classes.map(p => PrettyPrinter(p._2, opts)).mkString("\n\n") +
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

trait TypeOps extends ast.TypeOps {
  protected val trees: Trees
  import trees._

  override def typeBound(t1: Type, t2: Type, isLub: Boolean, allowSub: Boolean)
                        (implicit freeParams: Seq[TypeParameter]): Option[(Type, Map[TypeParameter, Type])] = {
    (t1, t2) match {
      case (ct: ClassType, _) if !ct.lookupClass.isDefined => None
      case (_, ct: ClassType) if !ct.lookupClass.isDefined => None

      case (ct1: ClassType, ct2: ClassType) =>
        val cd1 = ct1.tcd.cd
        val cd2 = ct2.tcd.cd
        val bound: Option[ClassDef] = if (allowSub) {
          val an1 = cd1 +: cd1.ancestors
          val an2 = cd2 +: cd2.ancestors
          if (isLub) {
            (an1.reverse zip an2.reverse)
              .takeWhile(((_: ClassDef) == (_: ClassDef)).tupled)
              .lastOption.map(_._1)
          } else {
            if (an1.contains(cd2)) Some(cd1)
            else if (an2.contains(cd1)) Some(cd2)
            else None
          }
        } else {
          if (cd1 == cd2) Some(cd1) else None
        }

        for {
          cd <- bound
          (subs, map) <- flattenTypeMappings((ct1.tps zip ct2.tps).map { case (tp1, tp2) =>
            typeBound(tp1, tp2, isLub, allowSub = false)
          })
        } yield (cd.typed(subs).toType, map)

      case _ => super.typeBound(t1, t2, isLub, allowSub)
    }
  }
  
}
