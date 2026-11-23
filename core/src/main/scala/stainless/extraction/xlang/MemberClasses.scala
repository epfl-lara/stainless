/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package xlang

import stainless.ast.{Symbol, SymbolIdentifier}
import scala.collection.mutable.{Map => MutableMap}

/** Lifts member classes, which refer to an instance of their enclosing class.
 *
 *  The frontend extracts a member class `C` defined in the body of the class `O` as a class with
 *  the [[IsMemberOf]]`(O)` flag, and `O.this` within `C` as `This(O)`. The path-dependent type `p.C`
 *  is a [[PathType]], and `new p.C(args)` and `case p.C(pats)` are a [[PathClassConstructor]] and
 *  a [[PathClassPattern]]. For example,
 *
 * {{{
 * class Box(val n: BigInt) {
 *   case class Item(v: BigInt) {
 *     def total: BigInt = v + Box.this.n
 *   }
 *   def mk(v: BigInt): Item = Item(v)
 * }
 * def isItemOf(b: Box, e: Any): Boolean = e match {
 *   case b.Item(_) => true
 *   case _ => false
 * }
 * }}}
 *
 *  This phase gives each concrete member class a field holding its outer instance, and each member
 *  class an accessor for it, as Scala does. The accessors of a hierarchy of member classes override
 *  each other (abstract member classes may narrow the type of the outer instance). It then
 *
 *  - replaces `O.this` within `C` with `this.outer` (or `this.outer.outer`, etc.),
 *  - passes the outer instance to constructors, and tests it in patterns,
 *  - encodes `p.C` as `{ x: C | x.outer eq p }`, and tests the outer instance in type tests and
 *    patterns on `p.C` (as emitted by the frontend for `case _: p.C`, but not for `isInstanceOf[p.C]`,
 *    which doesn't test the outer instance in Scala),
 *  - replaces a field type `p.C` where `p` refers to `this` with `C`, and constrains the field in
 *    the class invariant instead (or drops the constraint when nested, as in `List[p.C]`).
 *
 *  The example becomes
 *
 * {{{
 * case class Item(outer: Box, v: BigInt) {
 *   def total: BigInt = v + this.outer.n
 * }
 * class Box(val n: BigInt) {
 *   def mk(v: BigInt): { x: Item | x.outer eq this } = Item(this, v)
 * }
 * def isItemOf(b: Box, e: Any): Boolean = e match {
 *   case Item(o, _) if o eq b => true
 *   case _ => false
 * }
 * }}}
 *
 *  The members of a member class of a generic class `O[A]` may mention `A`, which the outer instance
 *  instantiates (see [[Trees.outerTypeSubst]]), as methods mention the type parameters of their class.
 *  As [[methods.MethodLifting]] does for methods, this phase lifts the member class with the type parameters
 *  of `O` followed by its own: the type `p.C`, where `p: O[S]`, becomes `C[S]` (refined with the outer test).
 *  A member class may also extend a member class of a generic ancestor of its enclosing class, which instantiates
 *  it: in `trait IntLang extends Lang[BigInt] { case class Neg(e: Expr) extends Expr }`, `Neg` extends `Expr[BigInt]`.
 *  Its outer tests use an outer accessor with type `Any` (see `hasGenericOuter`).
 *
 *  The reference equalities `eq` are lowered by [[OuterIdentities]].
 */
class MemberClasses(override val s: Trees)(override val t: s.type)
                   (using override val context: inox.Context) extends ExtractionPipeline { self =>
  import s._

  override def invalidate(id: Identifier): Unit = ()

  // The binder is the same for all types `p.C`, so that types with the same path are equal
  private val binders = MutableMap[Identifier, Identifier]()
  private val outerFields = MutableMap[Identifier, Identifier]()
  private val outerAccessors = MutableMap[Identifier, Identifier]()
  private val outerAccessorSymbols = MutableMap[Identifier, Symbol]()
  private val outerRefAccessors = MutableMap[Identifier, Identifier]()
  private lazy val invSymbol = Symbol("inv")

  private def fullName(id: Identifier): String = id match {
    case sid: SymbolIdentifier => sid.symbol.name
    case _ => id.name
  }

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    given s.Symbols = symbols

    def ownerOf(id: Identifier): Option[Identifier] =
      symbols.lookupClass(id).flatMap(_.flags.collectFirst { case IsMemberOf(owner) => owner })

    def isMember(id: Identifier): Boolean = ownerOf(id).isDefined
    def isAbstract(id: Identifier): Boolean = symbols.lookupClass(id).exists(_.flags contains IsAbstract)

    if (!symbols.classes.keys.exists(isMember)) return (symbols, ExtractionSummary.NoSummary)

    def parents(id: Identifier): Seq[Identifier] = symbols.lookupClass(id).toSeq.flatMap(_.parents.map(_.id))

    /** The class `id` and its ancestors, from the class to its farthest ancestors. */
    def ancestors(id: Identifier): Seq[Identifier] = {
      def rec(id: Identifier): Seq[Identifier] = id +: parents(id).flatMap(rec)
      rec(id).reverse.distinct.reverse
    }

    def derivesFrom(id: Identifier, ancestor: Identifier): Boolean = ancestors(id) contains ancestor

    /** The member class ancestors of the member class `id`, excluding `id`. */
    def memberParents(id: Identifier): Seq[Identifier] = parents(id).filter(isMember)

    /** Whether the member class `id` declares an outer accessor: it does if it is concrete, or if it is
      * abstract and its member class ancestors, if any, are abstract and belong to another outer class
      * (in which case the accessor is narrowed).
      */
    def declaresOuterAccessor(id: Identifier): Boolean =
      !isAbstract(id) || {
        val ps = memberParents(id)
        ps.isEmpty || ps.forall(p => isAbstract(p) && ownerOf(p) != ownerOf(id))
      }

    /** The class declaring the outer accessor that the member class `id` inherits (possibly `id` itself). */
    def outerAccessorOwner(id: Identifier): Identifier =
      if (declaresOuterAccessor(id)) id else outerAccessorOwner(memberParents(id).head)

    /** The outer accessor declared by the member class `id`, which overrides those of its member class ancestors. */
    def outerAccessorId(id: Identifier): Identifier = outerAccessors.getOrElseUpdate(id, {
      val root = ancestors(id).filter(isMember).last
      SymbolIdentifier(outerAccessorSymbols.getOrElseUpdate(root, Symbol(fullName(root) + ".outer")))
    })

    def outerFieldId(id: Identifier): Identifier =
      outerFields.getOrElseUpdate(id, SymbolIdentifier(fullName(id) + ".$outer"))

    /** The type of `this` within the class `id`: its self type, if any (see [[SelfTypes]]). */
    def thisType(id: Identifier): ClassType =
      symbols.lookupClass(id).flatMap(_.flags.collectFirst { case SelfType(tpe) => tpe }).getOrElse(ClassType(id, symbols.getClass(id).typeArgs))

    /** The type of the outer instance of the member class `id`, within `id` (before lifting the type parameters). */
    def outerType(id: Identifier): ClassType = thisType(ownerOf(id).get)

    /** The type parameters of the class `id` once lifted: those of its enclosing classes, then its own. */
    def liftedTypeParams(id: Identifier): Seq[TypeParameterDef] =
      ownerOf(id).toSeq.flatMap(liftedTypeParams) ++ symbols.getClass(id).tparams

    /** The lifted type parameters of the member class `id` that come from its enclosing classes. */
    def outerTypeParams(id: Identifier): Seq[TypeParameterDef] = ownerOf(id).toSeq.flatMap(liftedTypeParams)

    /** The outer instance of `e`, an instance of the member class `id`, and its type. */
    def selectOuter(e: Expr, id: Identifier): (Expr, ClassType) = {
      val owner = outerAccessorOwner(id)
      (MethodInvocation(e, outerAccessorId(owner), Seq.empty, Seq.empty).copiedFrom(e), outerType(owner))
    }

    /** Whether the member class `id` belongs to a generic class, or extends a member class of a generic class.
      *
      * The outer accessor of such member classes returns an instance of a generic class, whose type parameters
      * TypeEncoding encodes in every function that calls it, including the class invariants that constrain
      * fields of type `p.C` (which must then box the values of these type parameters). Outer tests on such
      * member classes therefore use a ghost accessor of the outer instance with type `Any` instead, which
      * [[OuterIdentities]] pairs with a copy of the identity of the outer instance.
      */
    def hasGenericOuter(id: Identifier): Boolean = ancestors(id).exists(outerTypeParams(_).nonEmpty)

    def outerRefId(id: Identifier): Identifier =
      outerRefAccessors.getOrElseUpdate(id, SymbolIdentifier(MemberClasses.outerRefSymbol))

    /** The outer instance of `e`, an instance of the member class `id` with a generic outer, with type `Any`. */
    def selectOuterRef(e: Expr, id: Identifier): Expr =
      MethodInvocation(e, outerRefId(outerAccessorOwner(id)), Seq.empty, Seq.empty).copiedFrom(e)

    /** The classes whose `this` is accessible within the class `id`, innermost first. */
    def enclosing(id: Identifier): Seq[Identifier] = id +: ownerOf(id).toSeq.flatMap(enclosing)

    def mentionsThis(e: Expr): Boolean = exprOps.exists { case _: This => true case _ => false } (e)

    /** Fields of type `p.C` where `p` refers to `this` (or `O.this`) are constrained by the class invariant. */
    val fieldInvariants: Map[Identifier, Seq[Expr]] = symbols.classes.values.map { cd =>
      val ct = ClassType(cd.id, cd.typeArgs).copiedFrom(cd)
      cd.id -> cd.fields.flatMap { vd =>
        vd.tpe match {
          case pt @ PathType(path, _) if mentionsThis(path) =>
            Some(IsInstanceOf(ClassSelector(This(ct).copiedFrom(vd), vd.id).copiedFrom(vd), pt).copiedFrom(vd))
          case _ => None
        }
      }
    }.filter(_._2.nonEmpty).toMap

    def stripThisPaths(tpe: Type): Type = typeOps.postMap {
      case PathType(path, ct) if mentionsThis(path) => Some(ct)
      case _ => None
    } (tpe)

    class Transformer(cls: Option[Identifier]) extends ConcreteOOSelfTreeTransformer(self.s, self.s) {
      private val classes = cls.toSeq.flatMap(enclosing)

      private def outerTest(e: Expr, ct: ClassType, path: Expr): Expr =
        if (!hasGenericOuter(ct.id)) RefEquals(selectOuter(e, ct.id)._1, transform(path)).copiedFrom(path)
        else transform(path) match {
          // The outer instance of `this`, an instance of a member class with a generic outer
          case OuterOfThis(ths, tct) => RefEquals(selectOuterRef(e, ct.id), selectOuterRef(ths, tct.id)).copiedFrom(path)
          case tpath => RefEquals(selectOuterRef(e, ct.id), tpath).copiedFrom(path)
        }

      /** The outer instance of `this`, possibly cast, where `this` is an instance of a member class with a generic outer. */
      private object OuterOfThis {
        def unapply(e: Expr): Option[(Expr, ClassType)] = e match {
          case AsInstanceOf(OuterOfThis(ths, tct), _) => Some((ths, tct))
          case MethodInvocation(ths @ This(tct), id, Seq(), Seq())
              if hasGenericOuter(tct.id) && id == outerAccessorId(outerAccessorOwner(tct.id)) => Some((ths, tct))
          case _ => None
        }
      }

      /** The type arguments of the classes enclosing `cls` and its ancestors, as seen within `cls`. */
      private lazy val contextSubst: Map[TypeParameter, Type] = cls match {
        case Some(id) => ancestorsTypeSubst(ClassType(id, symbols.getClass(id).typeArgs), enclosingTypeSubst(id))
        case None => Map.empty
      }

      /** The class type `ct`, with the type arguments of its enclosing classes, given by the outer instance `path`
        * if any, or otherwise by the classes enclosing `cls` (or by their type parameters, as within these classes). */
      private def liftType(ct: ClassType, path: Option[Expr]): ClassType = {
        val subst = path.map(outerTypeSubst(_, ct.id)).getOrElse(contextSubst)
        val outerTps = outerTypeParams(ct.id).map(tpd => subst.getOrElse(tpd.tp, tpd.tp))
        ClassType(ct.id, (outerTps ++ ct.tps).map(transform)).copiedFrom(ct)
      }

      /** The type of the outer instance of an instance of the (lifted) class type `ct`, a member class. */
      private def outerTypeOf(ct: ClassType): Type =
        typeOps.instantiateType(transform(outerType(ct.id)), (liftedTypeParams(ct.id).map(_.tp) zip ct.tps).toMap)

      override def transform(tpe: Type): Type = tpe match {
        case PathType(path, ct) =>
          val tct = liftType(ct, Some(path))
          val vd = ValDef(binders.getOrElseUpdate(ct.id, FreshIdentifier("x")), tct).copiedFrom(tpe)
          RefinementType(vd, outerTest(vd.toVariable, ct, path)).copiedFrom(tpe)
        case ct @ ClassType(id, tps) if isMember(id) && tps.size == symbols.getClass(id).tparams.size && outerTypeParams(id).nonEmpty =>
          liftType(ct, None)
        case _ => super.transform(tpe)
      }

      override def transform(e: Expr): Expr = e match {
        // `O.this` within a member class nested in `O`
        case This(ct) if classes.size >= 2 && !derivesFrom(classes.head, ct.id) =>
          val idx = classes.indexWhere(c => derivesFrom(c, ct.id) || derivesFrom(thisType(c).id, ct.id))
          if (idx < 0) context.reporter.fatalError(e.getPos, s"Cannot access ${ct.id.asString} from ${classes.head.asString}")
          var res: Expr = This(transform(ClassType(classes.head, symbols.getClass(classes.head).typeArgs)).asInstanceOf[ClassType]).copiedFrom(e)
          for (i <- 0 until idx) {
            val (outer, tpe) = selectOuter(res, classes(i))
            // The inherited accessor may have a wider type than the class enclosing `classes(i)`
            res = if (tpe == thisType(classes(i + 1))) outer else AsInstanceOf(outer, transform(thisType(classes(i + 1)))).copiedFrom(e)
          }
          res

        case PathClassConstructor(path, ct, args) =>
          ClassConstructor(liftType(ct, Some(path)), (path +: args).map(transform)).copiedFrom(e)

        case ClassConstructor(ct, _) if isMember(ct.id) =>
          context.reporter.fatalError(e.getPos, s"Unknown outer instance for the construction of ${ct.id.asString}")

        case IsInstanceOf(expr, PathType(path, ct)) =>
          val te = transform(expr)
          val tct = liftType(ct, Some(path))
          if (symbols.isSubtypeOf(expr.getType, ct)) outerTest(te, ct, path)
          else And(IsInstanceOf(te, tct).copiedFrom(e), outerTest(AsInstanceOf(te, tct).copiedFrom(e), ct, path)).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(pat: Pattern): Pattern = pat match {
        case InstanceOfPattern(binder, PathType(path, ct)) =>
          val tct = liftType(ct, Some(path))
          val vd = ValDef.fresh("x", tct).copiedFrom(pat)
          RefinementPattern(
            InstanceOfPattern(binder.map(transform), tct).copiedFrom(pat),
            Lambda(Seq(vd), outerTest(vd.toVariable, ct, path)).copiedFrom(pat)
          ).copiedFrom(pat)

        case PathClassPattern(binder, path, ct, subs) =>
          val tct = liftType(ct, Some(path))
          val vd = ValDef.fresh("outer", outerTypeOf(tct)).copiedFrom(pat)
          val outer = RefinementPattern(
            WildcardPattern(None).copiedFrom(pat),
            Lambda(Seq(vd), RefEquals(vd.toVariable, transform(path)).copiedFrom(pat)).copiedFrom(pat)
          ).copiedFrom(pat)
          ClassPattern(binder.map(transform), tct, outer +: subs.map(transform)).copiedFrom(pat)

        case ClassPattern(binder, ct, subs) if isMember(ct.id) =>
          ClassPattern(binder.map(transform), transform(ct).asInstanceOf[ClassType],
            WildcardPattern(None).copiedFrom(pat) +: subs.map(transform)).copiedFrom(pat)

        case _ => super.transform(pat)
      }
    }

    def ownerClass(flags: Seq[Flag]): Option[Identifier] = flags.collectFirst {
      case IsMethodOf(id) => id
      case IsTypeMemberOf(id) => id
    }

    // The outer accessors, marked for [[OuterIdentities]]
    val outerAccessorFlag = Annotation("outerAccessor", Seq.empty)
    val accessors: Seq[FunDef] = symbols.classes.values.toSeq.filter(cd => isMember(cd.id) && declaresOuterAccessor(cd.id)).map { cd =>
      val ct = ClassType(cd.id, cd.typeArgs).copiedFrom(cd)
      val tpe = outerType(cd.id).copiedFrom(cd)
      if (isAbstract(cd.id)) {
        // An abstract method rather than an abstract value, so that abstract member classes can narrow it
        new FunDef(outerAccessorId(cd.id), Seq.empty, Seq.empty, tpe, NoTree(tpe).copiedFrom(cd),
          Seq(IsAbstract, outerAccessorFlag, IsMethodOf(cd.id))).copiedFrom(cd)
      } else {
        new FunDef(outerAccessorId(cd.id), Seq.empty, Seq.empty, tpe,
          ClassSelector(This(ct).copiedFrom(cd), outerFieldId(cd.id)).copiedFrom(cd),
          Seq(IsAccessor(Some(outerFieldId(cd.id))), outerAccessorFlag, IsMethodOf(cd.id))).copiedFrom(cd)
      }
    }

    // The outer accessors with type `Any`, see `hasGenericOuter`
    val outerRefs: Seq[FunDef] = symbols.classes.values.toSeq.filter(cd => isMember(cd.id) && declaresOuterAccessor(cd.id) && hasGenericOuter(cd.id)).map { cd =>
      val ct = ClassType(cd.id, cd.typeArgs).copiedFrom(cd)
      val tpe = AnyType().copiedFrom(cd)
      if (isAbstract(cd.id)) {
        new FunDef(outerRefId(cd.id), Seq.empty, Seq.empty, tpe, NoTree(tpe).copiedFrom(cd),
          Seq(IsAbstract, Ghost, IsMethodOf(cd.id))).copiedFrom(cd)
      } else {
        new FunDef(outerRefId(cd.id), Seq.empty, Seq.empty, tpe,
          ClassSelector(This(ct).copiedFrom(cd), outerFieldId(cd.id)).copiedFrom(cd),
          Seq(IsAccessor(Some(outerFieldId(cd.id))), Ghost, IsMethodOf(cd.id))).copiedFrom(cd)
      }
    }

    // The class invariants, extended with the constraints on fields
    val (invariants, newInvariants) = {
      val existing = symbols.functions.values.filter(_.flags contains IsInvariant).flatMap { fd =>
        ownerClass(fd.flags).filter(fieldInvariants.contains).map(_ -> fd)
      }.toMap
      // Invariants override each other, and share the same symbol
      val sym = symbols.functions.values.find(_.flags contains IsInvariant).map(_.id).collect {
        case sid: SymbolIdentifier => sid.symbol
      }.getOrElse(invSymbol)
      val updated = existing.map { case (cid, fd) =>
        fd.copy(fullBody = andJoin(fieldInvariants(cid) :+ fd.fullBody).copiedFrom(fd)).copiedFrom(fd)
      }
      val added = fieldInvariants.filterNot(p => existing.contains(p._1)).map { case (cid, invs) =>
        val cd = symbols.getClass(cid)
        val flags = cd.flags.filter {
          case IsAbstract | IsExtensible | IsSealed | ValueClass | IsCaseObject | IsMutable | IsObject | IsMemberOf(_) | IsTrait | SelfType(_) => false
          case f => f.name != "cCode.export" && !f.name.startsWith("cCode.global")
        }
        new FunDef(SymbolIdentifier(sym), Seq.empty, Seq.empty, BooleanType().copiedFrom(cd), andJoin(invs).copiedFrom(cd),
          Seq(IsInvariant, IsMethodOf(cid)) ++ flags).copiedFrom(cd)
      }
      (updated.toSeq, added.toSeq)
    }
    val invariantIds = invariants.map(_.id).toSet

    val functions = (symbols.functions.values.filterNot(fd => invariantIds(fd.id)) ++ invariants ++ newInvariants ++ accessors ++ outerRefs).map { fd =>
      new Transformer(ownerClass(fd.flags)).transform(fd)
    }

    val classes = symbols.classes.values.map { cd =>
      val fields = cd.fields.map(vd => vd.copy(tpe = stripThisPaths(vd.tpe)).copiedFrom(vd))
      val outerField =
        if (!isMember(cd.id) || isAbstract(cd.id)) None
        else Some(ValDef(outerFieldId(cd.id), outerType(cd.id).copiedFrom(cd)).copiedFrom(cd))
      new Transformer(Some(cd.id)).transform(cd.copy(tparams = liftedTypeParams(cd.id), fields = outerField.toSeq ++ fields).copiedFrom(cd))
    }

    val typeDefs = symbols.typeDefs.values.map(td => new Transformer(ownerClass(td.flags)).transform(td))

    val newSymbols = NoSymbols
      .withFunctions(functions.toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withClasses(classes.toSeq)
      .withTypeDefs(typeDefs.toSeq)

    (newSymbols, ExtractionSummary.NoSummary)
  }
}

object MemberClasses {
  /** The symbol shared by the outer accessors with type `Any` of member classes with a generic outer, which
    * [[OuterIdentities]] recognizes. Their type doesn't depend on the outer class, so they all override each other. */
  private[xlang] val outerRefSymbol: Symbol = Symbol("stainless.lang.outerRef")

  def apply(trees: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends MemberClasses(s)(t)
    new Impl(trees, trees)
  }
}
