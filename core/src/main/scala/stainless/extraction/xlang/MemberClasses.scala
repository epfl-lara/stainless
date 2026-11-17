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
      symbols.lookupClass(id).flatMap(_.flags.collectFirst { case SelfType(tpe) => tpe }).getOrElse(ClassType(id, Seq.empty))

    def outerType(id: Identifier): ClassType = thisType(ownerOf(id).get)

    /** The outer instance of `e`, an instance of the member class `id`, and its type. */
    def selectOuter(e: Expr, id: Identifier): (Expr, ClassType) = {
      val owner = outerAccessorOwner(id)
      (MethodInvocation(e, outerAccessorId(owner), Seq.empty, Seq.empty).copiedFrom(e), outerType(owner))
    }

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
        RefEquals(selectOuter(e, ct.id)._1, transform(path)).copiedFrom(path)

      override def transform(tpe: Type): Type = tpe match {
        case PathType(path, ct) =>
          val tct = transform(ct).asInstanceOf[ClassType]
          val vd = ValDef(binders.getOrElseUpdate(ct.id, FreshIdentifier("x")), tct).copiedFrom(tpe)
          RefinementType(vd, outerTest(vd.toVariable, ct, path)).copiedFrom(tpe)
        case _ => super.transform(tpe)
      }

      override def transform(e: Expr): Expr = e match {
        // `O.this` within a member class nested in `O`
        case This(ct) if classes.size >= 2 && !derivesFrom(classes.head, ct.id) =>
          val idx = classes.indexWhere(c => derivesFrom(c, ct.id) || derivesFrom(thisType(c).id, ct.id))
          if (idx < 0) context.reporter.fatalError(e.getPos, s"Cannot access ${ct.id.asString} from ${classes.head.asString}")
          var res: Expr = This(ClassType(classes.head, symbols.getClass(classes.head).typeArgs)).copiedFrom(e)
          for (i <- 0 until idx) {
            val (outer, tpe) = selectOuter(res, classes(i))
            // The inherited accessor may have a wider type than the class enclosing `classes(i)`
            res = if (tpe == thisType(classes(i + 1))) outer else AsInstanceOf(outer, thisType(classes(i + 1))).copiedFrom(e)
          }
          res

        case PathClassConstructor(path, ct, args) =>
          ClassConstructor(transform(ct).asInstanceOf[ClassType], (path +: args).map(transform)).copiedFrom(e)

        case ClassConstructor(ct, _) if isMember(ct.id) =>
          context.reporter.fatalError(e.getPos, s"Unknown outer instance for the construction of ${ct.id.asString}")

        case IsInstanceOf(expr, PathType(path, ct)) =>
          val te = transform(expr)
          val tct = transform(ct).asInstanceOf[ClassType]
          if (symbols.isSubtypeOf(expr.getType, ct)) outerTest(te, ct, path)
          else And(IsInstanceOf(te, tct).copiedFrom(e), outerTest(AsInstanceOf(te, tct).copiedFrom(e), ct, path)).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(pat: Pattern): Pattern = pat match {
        case InstanceOfPattern(binder, PathType(path, ct)) =>
          val tct = transform(ct).asInstanceOf[ClassType]
          val vd = ValDef.fresh("x", tct).copiedFrom(pat)
          RefinementPattern(
            InstanceOfPattern(binder.map(transform), tct).copiedFrom(pat),
            Lambda(Seq(vd), outerTest(vd.toVariable, ct, path)).copiedFrom(pat)
          ).copiedFrom(pat)

        case PathClassPattern(binder, path, ct, subs) =>
          val vd = ValDef.fresh("outer", outerType(ct.id)).copiedFrom(pat)
          val outer = RefinementPattern(
            WildcardPattern(None).copiedFrom(pat),
            Lambda(Seq(vd), RefEquals(vd.toVariable, transform(path)).copiedFrom(pat)).copiedFrom(pat)
          ).copiedFrom(pat)
          ClassPattern(binder.map(transform), transform(ct).asInstanceOf[ClassType], outer +: subs.map(transform)).copiedFrom(pat)

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

    // The outer accessors
    val accessors: Seq[FunDef] = symbols.classes.values.toSeq.filter(cd => isMember(cd.id) && declaresOuterAccessor(cd.id)).map { cd =>
      val ct = ClassType(cd.id, cd.typeArgs).copiedFrom(cd)
      val tpe = outerType(cd.id).copiedFrom(cd)
      if (isAbstract(cd.id)) {
        // An abstract method rather than an abstract value, so that abstract member classes can narrow it
        new FunDef(outerAccessorId(cd.id), Seq.empty, Seq.empty, tpe, NoTree(tpe).copiedFrom(cd),
          Seq(IsAbstract, IsMethodOf(cd.id))).copiedFrom(cd)
      } else {
        new FunDef(outerAccessorId(cd.id), Seq.empty, Seq.empty, tpe,
          ClassSelector(This(ct).copiedFrom(cd), outerFieldId(cd.id)).copiedFrom(cd),
          Seq(IsAccessor(Some(outerFieldId(cd.id))), IsMethodOf(cd.id))).copiedFrom(cd)
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
          case IsAbstract | IsSealed | ValueClass | IsCaseObject | IsMutable | IsObject | IsMemberOf(_) | IsTrait | SelfType(_) => false
          case f => f.name != "cCode.export" && !f.name.startsWith("cCode.global")
        }
        new FunDef(SymbolIdentifier(sym), Seq.empty, Seq.empty, BooleanType().copiedFrom(cd), andJoin(invs).copiedFrom(cd),
          Seq(IsInvariant, IsMethodOf(cid)) ++ flags).copiedFrom(cd)
      }
      (updated.toSeq, added.toSeq)
    }
    val invariantIds = invariants.map(_.id).toSet

    val functions = (symbols.functions.values.filterNot(fd => invariantIds(fd.id)) ++ invariants ++ newInvariants ++ accessors).map { fd =>
      new Transformer(ownerClass(fd.flags)).transform(fd)
    }

    val classes = symbols.classes.values.map { cd =>
      val fields = cd.fields.map(vd => vd.copy(tpe = stripThisPaths(vd.tpe)).copiedFrom(vd))
      val outerField =
        if (!isMember(cd.id) || isAbstract(cd.id)) None
        else Some(ValDef(outerFieldId(cd.id), outerType(cd.id).copiedFrom(cd)).copiedFrom(cd))
      new Transformer(Some(cd.id)).transform(cd.copy(fields = outerField.toSeq ++ fields).copiedFrom(cd))
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
  def apply(trees: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends MemberClasses(s)(t)
    new Impl(trees, trees)
  }
}
