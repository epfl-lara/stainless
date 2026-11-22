/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package xlang

trait Trees extends innerclasses.Trees { self =>

  case object Ignore extends Flag("ignore", Seq.empty)

  /** Strictness flag for bitvector types that cannot be cast implicitly */
  case object StrictBV extends Flag("strict-bv", Seq.empty)

  /** The class is a member class of the class `id`: it is defined in the body of `id` (see [[MemberClasses]]). */
  case class IsMemberOf(id: Identifier) extends Flag("memberOf", Seq(id))

  /** The class is the class of an object. */
  case object IsObject extends Flag("object", Seq.empty)

  /** The class is a trait, which can be mixed in (see [[Mixins]]). */
  case object IsTrait extends Flag("trait", Seq.empty)

  /** The class declares the self type `tpe`, a subclass of the class: `this` is an instance of `tpe` within the class. */
  case class SelfType(tpe: ClassType) extends Flag("selfType", Seq(tpe))

  override def extractFlag(name: String, args: Seq[Expr]): Flag = (name, args) match {
    case ("ignore", Seq()) => Ignore
    case _ => super.extractFlag(name, args)
  }

  /** $encodingof `path.C`, where `C` is a member class: the instances of `C` whose outer instance is `path`
    *
    * Lowered to a refinement of `tpe` by [[MemberClasses]].
    */
  case class PathType(path: Expr, tpe: ClassType) extends Type {
    override protected def computeErasedType(using Symbols): Type = tpe.getType
    override def stripToplevelRefinement: Type = tpe
  }

  // Path-dependent types are refinements of their class type
  override protected def widenTypeParameter(tpe: Typed)(using Symbols): Type = super.widenTypeParameter(tpe) match {
    case PathType(_, ct) => widenTypeParameter(ct)
    case tpe => tpe
  }

  private def ownerOf(id: Identifier)(using s: Symbols): Option[Identifier] =
    s.lookupClass(id).flatMap(_.flags.collectFirst { case IsMemberOf(owner) => owner })

  /** The instantiation of the type parameters of the ancestors of the class type `ct`, and of their enclosing classes. */
  def ancestorsTypeSubst(ct: ClassType, outerSubst: Map[TypeParameter, Type])(using s: Symbols): Map[TypeParameter, Type] = {
    val subst = ct.lookupClass.toSeq.flatMap(tcd => tcd +: tcd.ancestors).flatMap(_.tpSubst).toMap
    subst.view.mapValues(typeOps.instantiateType(_, outerSubst)).toMap ++ outerSubst
  }

  /** The instantiation of the type parameters of the classes enclosing the member class `id`, given by its outer instance `path`.
    *
    * The members of a member class may mention the type parameters of its enclosing classes, as methods mention the type
    * parameters of their class. Just as the receiver of a method gives the type arguments of its class, the outer instance
    * of an instance of a member class gives those of its enclosing classes. The member class may also extend member classes
    * of ancestors of its enclosing class, whose type parameters the type of the outer instance instantiates as well.
    */
  def outerTypeSubst(path: Expr, id: Identifier)(using s: Symbols): Map[TypeParameter, Type] =
    if (ownerOf(id).isEmpty) Map.empty
    else widenTypeParameter(path) match {
      // The enclosing class may itself be a member class
      case pct: ClassType => ancestorsTypeSubst(pct, memberTypeSubst(path))
      case _ => Map.empty
    }

  /** The instantiation of the type parameters of the classes enclosing the class `id` within `id`, and of the
    * enclosing classes of its ancestors: those of the enclosing classes of `id` stay free, as in the body of `id`. */
  def enclosingTypeSubst(id: Identifier)(using s: Symbols): Map[TypeParameter, Type] = ownerOf(id) match {
    case Some(owner) => s.lookupClass(owner) match {
      case Some(ocd) => ancestorsTypeSubst(ClassType(owner, ocd.typeArgs), enclosingTypeSubst(owner))
      case None => Map.empty
    }
    case None => Map.empty
  }

  override protected def memberTypeSubst(e: Expr)(using s: Symbols): Map[TypeParameter, Type] = {
    def rec(tpe: Type): Map[TypeParameter, Type] = tpe match {
      case PathType(path, ct) => outerTypeSubst(path, ct.id)
      // A member class type without a path, as the type of `this` within the member class
      case ct: ClassType => enclosingTypeSubst(ct.id)
      case AnnotatedType(tpe, _) => rec(tpe)
      case RefinementType(vd, _) => rec(vd.tpe)
      case _ => Map.empty
    }
    if (!isMemberClassType(widenTypeParameter(e))) Map.empty
    else rec(e.getTpe(stripRefinements = false)).filter { case (tp, tpe) => tp != tpe }
  }

  private def isMemberClassType(tpe: Type)(using s: Symbols): Boolean = tpe match {
    case ct: ClassType => ownerOf(ct.id).isDefined
    case _ => false
  }

  /** $encodingof `new path.C(args)`, where `C` is a member class */
  case class PathClassConstructor(path: Expr, ct: ClassType, args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeTpe(stripRefinements: Boolean)(using s: Symbols): Type = ct.lookupClass match {
      case Some(tcd) =>
        val subst = outerTypeSubst(path, ct.id)
        checkParamTypes(args.map(_.getType), tcd.fields.map(vd => typeOps.instantiateType(vd.tpe, subst)), PathType(path, ct))
      case None => Untyped
    }
  }

  /** $encodingof `case path.C(subPatterns)`, where `C` is a member case class */
  case class PathClassPattern(binder: Option[ValDef], path: Expr, tpe: ClassType, subPatterns: Seq[Pattern]) extends Pattern

  /** $encodingof `lhs eq rhs`
    *
    * Only supported on instances of classes with identities, currently the outer instances of member
    * classes: [[OuterIdentities]] lowers it to a comparison of both the instances and their identities.
    */
  case class RefEquals(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeTpe(stripRefinements: Boolean)(using Symbols): Type =
      if (lhs.isTyped && rhs.isTyped) BooleanType() else Untyped
  }

  /** $encodingof `import some.package.Path` or `import some.package.path._` */
  case class Import(path: Seq[String], isWildcard: Boolean) extends Tree

  /** $encodingof `package name; ...` */
  case class UnitDef(
    id: Identifier,
    imports: Seq[Import],
    classes: Seq[Identifier],
    modules: Seq[ModuleDef],
    isMain: Boolean
  ) extends Tree {
    def allClasses: Seq[Identifier] = modules.flatMap(_.allClasses) ++ classes

    def allFunctions(using s: Symbols): Seq[Identifier] =
      classes.flatMap(s.getClass(_).methods) ++
      modules.flatMap(_.allFunctions)

    def allTypeDefs: Seq[Identifier] = modules.flatMap(_.allTypeDefs)
  }

  /** $encodingof `object name { ... }` */
  case class ModuleDef(
    id: Identifier,
    imports: Seq[Import],
    classes: Seq[Identifier],
    functions: Seq[Identifier],
    typeDefs: Seq[Identifier],
    modules: Seq[ModuleDef]
  ) extends Tree {
    def allClasses: Seq[Identifier] = modules.flatMap(_.allClasses) ++ classes

    def allFunctions(using s: Symbols): Seq[Identifier] =
      classes.flatMap(s.getClass(_).methods) ++
      modules.flatMap(_.allFunctions) ++
      functions

    def allTypeDefs: Seq[Identifier] = modules.flatMap(_.allTypeDefs) ++ typeDefs
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: (Trees & that.type) => // The `& that.type` trick allows to convince scala that `tree` and `that` are actually equal...
      class DeconstructorImpl(override val s: self.type, override val t: tree.type & that.type) extends ConcreteTreeDeconstructor(s, t)
      new DeconstructorImpl(self, tree)

    case _ => super.getDeconstructor(that)
  }
}


trait Printer extends innerclasses.Printer {
  val trees: Trees
  import trees._

  protected def classes(cls: Seq[Identifier]): PrintWrapper = PrintWrapper {
    pctx ?=>
      withSymbols(cls.map(id => pctx.opts.symbols.flatMap(_.lookupClass(id)) match {
        case Some(cd) => Left(cd)
        case None => Right(id)
      }), "class")
  }

  override def ppBody(tree: Tree)(using PrinterContext): Unit = tree match {
    case PathType(path, tpe) =>
      p"$path.$tpe"

    case RefEquals(lhs, rhs) =>
      p"$lhs eq $rhs"

    case PathClassConstructor(path, ct, args) =>
      p"new $path.$ct${nary(args, ", ", "(", ")")}"

    case PathClassPattern(binder, path, ct, subs) =>
      binder.foreach(b => p"$b @ ")
      p"$path.$ct${nary(subs, ", ", "(", ")")}"

    case Import(path, isWildcard) =>
      p"import ${path.mkString(".")}"
      if (isWildcard) p"._"

    case UnitDef(id, imports, cls, subs, _) =>
      p"""|package $id
          |"""

      if (imports.nonEmpty) p"""|${nary(imports, "\n")}
                                |"""
      if (cls.nonEmpty)     p"""|
                                |${classes(cls)}
                                |"""
      if (subs.nonEmpty)    p"""|
                                |${nary(subs, "\n\n")}
                                |"""

    case ModuleDef(id, imports, cls, funs, tps, subs) =>
      p"""|object $id {
          |"""
      if (imports.nonEmpty) p"""|
                                |  ${nary(imports, "\n")}
                                |"""
      if (tps.nonEmpty)     p"""|
                                |  ${typeDefs(tps)}
                                |"""
      if (cls.nonEmpty)     p"""|
                                |  ${classes(cls)}
                                |"""
      if (funs.nonEmpty)    p"""|
                                |  ${functions(funs)}
                                |"""
      if (subs.nonEmpty)    p"""|
                                |  ${nary(subs, "\n\n")}
                                |"""
      p"|}"

    case _ => super.ppBody(tree)
  }
}

/** Classes depend on their enclosing class and on their self type, which the phases that encode them read. */
trait DependencyGraph extends innerclasses.DependencyGraph {
  import inox.utils.Graphs._
  protected val trees: Trees
  import trees._

  override protected def computeDependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = super.computeDependencyGraph
    for (cd <- symbols.classes.values; flag <- cd.flags) flag match {
      case IsMemberOf(owner) => g += SimpleEdge(cd.id, owner)
      case SelfType(ct) => g += SimpleEdge(cd.id, ct.id)
      case _ =>
    }
    g
  }
}

trait SymbolOps extends innerclasses.TypeOps with throwing.SymbolOps { self =>
  protected val trees: Trees
  import trees._
  import symbols.{given, _}

  // Path-dependent types are refinements of their class type, see [[MemberClasses]]
  override protected def typeBound(tp1: Type, tp2: Type, upper: Boolean): Type = (tp1, tp2) match {
    case (pt1: PathType, pt2: PathType) if pt1 == pt2 => pt1
    case (pt: PathType, _) =>
      typeBound(pt.tpe, tp2, upper) match {
        case Untyped => Untyped
        case bound if !upper && bound == pt.tpe => pt
        case bound => bound
      }
    case (_, pt: PathType) =>
      typeBound(tp1, pt.tpe, upper) match {
        case Untyped => Untyped
        case bound if upper && bound == pt.tpe => pt
        case bound => bound
      }
    case _ => super.typeBound(tp1, tp2, upper)
  }

  override def patternInType(pat: Pattern): Type = pat match {
    case PathClassPattern(_, _, ct, _) => ct
    case _ => super.patternInType(pat)
  }

  override def patternIsTyped(in: Type, pat: Pattern): Boolean = pat match {
    case PathClassPattern(ob, path, ct, subs) =>
      // The fields may mention the type parameters of the enclosing classes, given by the outer instance
      val subst = outerTypeSubst(path, ct.id)
      ob.forall(vd => isSubtypeOf(ct, vd.getType)) &&
      lookupClass(ct.id).exists { cls =>
        cls.fields.size == subs.size &&
        cls.tparams.size == ct.tps.size &&
        (cls.typed(ct.tps).fields zip subs).forall { case (vd, sub) => patternIsTyped(typeOps.instantiateType(vd.getType, subst), sub) }
      }
    case _ => super.patternIsTyped(in, pat)
  }

  // The outer instance is not tested before [[MemberClasses]]
  override def mapForPattern(in: Expr, pattern: Pattern): Map[ValDef, Expr] = pattern match {
    case PathClassPattern(b, _, ct, subs) => super.mapForPattern(in, ClassPattern(b, ct, subs))
    case InstanceOfPattern(b, PathType(_, ct)) => super.mapForPattern(in, InstanceOfPattern(b, ct))
    case _ => super.mapForPattern(in, pattern)
  }

  protected class XlangPatternConditions[P <: PathLike[P]](includeBinders: Boolean)(using pp: PathProvider[P])
    extends OOPatternConditions[P](includeBinders) {
    override def apply(in: Expr, pattern: Pattern): P = pattern match {
      case PathClassPattern(b, _, ct, subs) => super.apply(in, ClassPattern(b, ct, subs))
      case InstanceOfPattern(b, PathType(_, ct)) => super.apply(in, InstanceOfPattern(b, ct))
      case _ => super.apply(in, pattern)
    }
  }

  override protected def patternConditions[P <: PathLike[P]](includeBinders: Boolean)(using PathProvider[P]) =
    new XlangPatternConditions[P](includeBinders)
}

trait GhostTraverser extends innerclasses.GhostTraverser {
  val trees: Trees
}

trait TreeDeconstructor extends innerclasses.TreeDeconstructor {

  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): Deconstructed[t.Expr] = e match {
    case s.RefEquals(lhs, rhs) =>
      (Seq(), Seq(), Seq(lhs, rhs), Seq(), Seq(), (_, _, es, _, _) => t.RefEquals(es(0), es(1)))
    case s.PathClassConstructor(path, ct, args) =>
      (Seq(), Seq(), path +: args, Seq(ct), Seq(), (_, _, es, tps, _) => t.PathClassConstructor(es.head, tps.head.asInstanceOf[t.ClassType], es.tail))
    case _ => super.deconstruct(e)
  }

  override def deconstruct(pattern: s.Pattern): DeconstructedPattern = pattern match {
    case s.PathClassPattern(binder, path, ct, subs) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(path), Seq(ct), subs, (_, vs, es, tps, subs) =>
        t.PathClassPattern(vs.headOption.map(_.toVal), es.head, tps.head.asInstanceOf[t.ClassType], subs))
    case _ => super.deconstruct(pattern)
  }

  override def deconstruct(tpe: s.Type): Deconstructed[t.Type] = tpe match {
    case s.PathType(path, ct) =>
      (Seq(), Seq(), Seq(path), Seq(ct), Seq(), (_, _, es, tps, _) => t.PathType(es.head, tps.head.asInstanceOf[t.ClassType]))
    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.Ignore => (Seq(), Seq(), Seq(), (_, _, _) => t.Ignore)
    case s.StrictBV => (Seq(), Seq(), Seq(), (_, _, _) => t.StrictBV)
    case s.IsMemberOf(id) => (Seq(id), Seq(), Seq(), (ids, _, _) => t.IsMemberOf(ids.head))
    case s.IsObject => (Seq(), Seq(), Seq(), (_, _, _) => t.IsObject)
    case s.IsTrait => (Seq(), Seq(), Seq(), (_, _, _) => t.IsTrait)
    case s.SelfType(tpe) => (Seq(), Seq(), Seq(tpe), (_, _, tps) => t.SelfType(tps.head.asInstanceOf[t.ClassType]))
    case _ => super.deconstruct(f)
  }
}

class ConcreteTreeDeconstructor(override val s: Trees, override val t: Trees) extends TreeDeconstructor