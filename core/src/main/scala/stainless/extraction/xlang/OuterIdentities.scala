/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package xlang

import stainless.ast.{Symbol, SymbolIdentifier}
import scala.collection.mutable.{Map => MutableMap}

/** Gives identities to outer instances, and encodes reference equality with them.
 *
 *  Scala tests outer instances of member classes with reference equality (see [[MemberClasses]]),
 *  which differs from structural equality for instances of (non-object) classes. Instances of
 *  classes with member classes (and of their subclasses) therefore get a ghost identity, read
 *  through an `identity` accessor. All objects share the identity `-1`, since structural equality
 *  already distinguishes them.
 *
 *  This phase lowers `a eq b` (a [[RefEquals]]) to the ghost comparison of both the instances
 *  and their identities, `a == b && a.identity == b.identity`. Each construction of an instance
 *  with an identity draws the next value of a ghost counter, held by an allocator that is passed
 *  as a ghost parameter to all functions that construct such instances, directly or through calls.
 *  As the counter only increases, identities drawn from the same allocator are distinct.
 *
 *  Instances of member classes of generic classes are tested through an outer accessor with type `Any`
 *  (see [[MemberClasses]]). They hold a ghost copy of the identity of their outer instance, set at
 *  construction, so that `x.outerRef eq p` is `x.outerRef == p && x.outerIdentity == p.identity`. For example,
 *
 * {{{
 * def mk(n: BigInt): Trees = new MyTrees(n)
 * def two: (Trees, Trees) = (mk(1), mk(1))
 * }}}
 *
 * becomes
 *
 * {{{
 * def mk(n: BigInt, @ghost alloc: Allocator): Trees = new MyTrees({
 *   @ghost val id = alloc.next
 *   @ghost alloc.next = id + 1
 *   id
 * }, n)
 * def two(@ghost alloc: Allocator): (Trees, Trees) = (mk(1, alloc), mk(1, alloc))
 * }}}
 */
class OuterIdentities(override val s: Trees)(override val t: s.type)
                     (using override val context: inox.Context) extends ExtractionPipeline { self =>
  import s._

  override def invalidate(id: Identifier): Unit = ()

  private val allocatorId = SymbolIdentifier("stainless.internal.Allocator")
  private val nextId = SymbolIdentifier("stainless.internal.Allocator.next")

  private def isFreshIdentity(e: Expr): Boolean = e match {
    case Annotated(NoTree(_), Seq(Annotation("freshIdentity", Seq()))) => true
    case _ => false
  }

  private def callees(fd: FunDef): Set[Identifier] = exprOps.collect[Identifier] {
    case FunctionInvocation(id, _, _) => Set(id)
    case MethodInvocation(_, id, _, _) => Set(id)
    case _ => Set()
  } (fd.fullBody)

  private val identityFields = MutableMap[Identifier, Identifier]()
  private val identityAccessors = MutableMap[Identifier, Identifier]()
  private val outerIdentityFields = MutableMap[Identifier, Identifier]()
  private val outerIdentityAccessors = MutableMap[Identifier, Identifier]()
  private lazy val outerIdentitySymbol = Symbol("stainless.lang.outerIdentity")
  // Identity accessors all override each other (a class may inherit them from unrelated traits)
  private lazy val identitySymbol = Symbol("stainless.lang.identity")

  private def fullName(id: Identifier): String = id match {
    case sid: SymbolIdentifier => sid.symbol.name
    case _ => id.name
  }

  /** Adds the identities of instances of classes with member classes, and lowers `a eq b`. */
  private def addIdentities(symbols: s.Symbols): s.Symbols = {
    given s.Symbols = symbols

    def flags(id: Identifier): Seq[Flag] = symbols.lookupClass(id).toSeq.flatMap(_.flags)
    def isObject(id: Identifier): Boolean = flags(id) contains IsObject
    def isAbstract(id: Identifier): Boolean = flags(id) contains IsAbstract

    val withMembers: Set[Identifier] = symbols.classes.values.flatMap(_.flags.collect { case IsMemberOf(id) => id })
      .filterNot(isObject).toSet
    if (withMembers.isEmpty) return symbols

    def ancestors(id: Identifier): Seq[Identifier] = {
      // Local classes are not in the symbols, and cannot be extended by global classes
      def rec(id: Identifier): Seq[Identifier] = id +: symbols.lookupClass(id).toSeq.flatMap(_.parents).flatMap(p => rec(p.id))
      rec(id).reverse.distinct.reverse
    }

    def hasIdentity(id: Identifier): Boolean = ancestors(id).exists(withMembers)

    /** Concrete classes implement the identity accessor, and abstract classes with member classes declare it. */
    def declaresIdentity(id: Identifier): Boolean = hasIdentity(id) && (!isAbstract(id) || withMembers(id))

    def identityAccessorId(id: Identifier): Identifier =
      identityAccessors.getOrElseUpdate(id, SymbolIdentifier(identitySymbol))

    def identityFieldId(id: Identifier): Identifier =
      identityFields.getOrElseUpdate(id, SymbolIdentifier(fullName(id) + ".$identity"))

    /** Whether instances of the class `id` are constructed with a fresh identity. */
    def hasIdentityField(id: Identifier): Boolean = hasIdentity(id) && !isAbstract(id) && !isObject(id)

    def selectIdentity(e: Expr, ct: ClassType): Expr = ancestors(ct.id).find(declaresIdentity) match {
      case Some(id) => MethodInvocation(e, identityAccessorId(id), Seq.empty, Seq.empty).copiedFrom(e)
      case None => context.reporter.fatalError(e.getPos, s"Instances of ${ct.id.asString} have no identity")
    }

    /** Whether the class `id` is (or extends) a member class of a generic class, which holds a copy of the identity of its outer instance. */
    def hasGenericOuter(id: Identifier): Boolean = ancestors(id).exists { aid =>
      flags(aid).collectFirst { case IsMemberOf(owner) => owner }.flatMap(symbols.lookupClass).exists(_.tparams.nonEmpty)
    }

    def hasOuterIdentityField(id: Identifier): Boolean = hasGenericOuter(id) && !isAbstract(id)

    def outerIdentityFieldId(id: Identifier): Identifier =
      outerIdentityFields.getOrElseUpdate(id, SymbolIdentifier(fullName(id) + ".$outerIdentity"))

    def outerIdentityAccessorId(id: Identifier): Identifier =
      outerIdentityAccessors.getOrElseUpdate(id, SymbolIdentifier(outerIdentitySymbol))

    /** The identity of the outer instance of `e`, an instance of a member class with a generic outer. */
    def selectOuterIdentity(e: Expr): Expr = e.getType match {
      case ct: ClassType => ancestors(ct.id).find(hasGenericOuter) match {
        case Some(id) => MethodInvocation(e, outerIdentityAccessorId(id), Seq.empty, Seq.empty).copiedFrom(e)
        case None => context.reporter.fatalError(e.getPos, s"Instances of ${ct.id.asString} have no outer identity")
      }
      case tpe => context.reporter.fatalError(e.getPos, s"Unexpected type ${tpe.asString} for an instance of a member class")
    }

    /** The outer instance with type `Any` of an instance of a member class with a generic outer (see [[MemberClasses]]). */
    object OuterRef {
      def unapply(e: Expr): Option[Expr] = e match {
        case MethodInvocation(rec, id: SymbolIdentifier, Seq(), Seq()) if id.symbol == MemberClasses.outerRefSymbol => Some(rec)
        case _ => None
      }
    }

    object transformer extends ConcreteOOSelfTreeTransformer(self.s, self.s) {
      override def transform(e: Expr): Expr = e match {
        case RefEquals(lhs, rhs) =>
          val (tl, tr) = (transform(lhs), transform(rhs))
          val ct = Seq(lhs.getType, rhs.getType).collectFirst { case ct: ClassType if hasIdentity(ct.id) => ct }
          val eq = Equals(tl, tr).copiedFrom(e)
          def identity(e: Expr, te: Expr): Option[Expr] = e match {
            case OuterRef(rec) => Some(selectOuterIdentity(transform(rec)))
            case _ => ct.map(selectIdentity(te, _))
          }
          val cmp = (identity(lhs, tl), identity(rhs, tr)) match {
            case (Some(il), Some(ir)) => And(eq, Equals(il, ir).copiedFrom(e)).copiedFrom(e)
            case _ => eq
          }
          Annotated(cmp, Seq(Ghost)).copiedFrom(e)

        case ClassConstructor(ct, args) if hasIdentityField(ct.id) || hasOuterIdentityField(ct.id) =>
          val targs = args.map(transform)
          // The outer instance comes first (see [[MemberClasses]])
          val withOuterIdentity =
            if (!hasOuterIdentityField(ct.id)) targs
            else args.head.getType.stripToplevelRefinement match {
              case oct: ClassType =>
                val outerIdentity = args.head match {
                  // The outer instance of `this`, whose identity `this` holds a copy of
                  case MethodInvocation(rec, id, Seq(), Seq())
                      if symbols.getFunction(id).flags.contains(Annotation("outerAccessor", Seq.empty)) &&
                         (rec.getType match { case rct: ClassType => hasGenericOuter(rct.id) case _ => false }) =>
                    selectOuterIdentity(transform(rec))
                  case _ => selectIdentity(targs.head, oct)
                }
                targs.head +: outerIdentity +: targs.tail
              case _ => context.reporter.fatalError(e.getPos, s"Unexpected outer instance of ${ct.id.asString}")
            }
          val withIdentity = if (hasIdentityField(ct.id)) freshIdentity(e) +: withOuterIdentity else withOuterIdentity
          ClassConstructor(transform(ct).asInstanceOf[ClassType], withIdentity).copiedFrom(e)

        case LetClass(lcds, _) if lcds.exists(_.parents.exists { case ct: ClassType => hasIdentity(ct.id) case _ => false }) =>
          context.reporter.fatalError(e.getPos, "Stainless does not support local or anonymous classes extending classes with member classes")

        case _ => super.transform(e)
      }

      override def transform(pat: Pattern): Pattern = pat match {
        case ClassPattern(binder, ct, subs) if hasIdentityField(ct.id) || hasOuterIdentityField(ct.id) =>
          val tsubs = subs.map(transform)
          val withOuterIdentity = if (hasOuterIdentityField(ct.id)) tsubs.head +: WildcardPattern(None).copiedFrom(pat) +: tsubs.tail else tsubs
          val withIdentity = if (hasIdentityField(ct.id)) WildcardPattern(None).copiedFrom(pat) +: withOuterIdentity else withOuterIdentity
          ClassPattern(binder.map(transform), transform(ct).asInstanceOf[ClassType], withIdentity).copiedFrom(pat)
        case _ => super.transform(pat)
      }
    }

    val accessors = symbols.classes.values.toSeq.filter(cd => declaresIdentity(cd.id)).map { cd =>
      val ct = ClassType(cd.id, cd.typeArgs).copiedFrom(cd)
      val tpe = IntegerType().copiedFrom(cd)
      val (body, flags) =
        if (isObject(cd.id)) (IntegerLiteral(-1).copiedFrom(cd), Seq())
        else if (isAbstract(cd.id)) (NoTree(tpe).copiedFrom(cd), Seq(IsAbstract))
        else (ClassSelector(This(ct).copiedFrom(cd), identityFieldId(cd.id)).copiedFrom(cd), Seq(IsAccessor(Some(identityFieldId(cd.id)))))
      new FunDef(identityAccessorId(cd.id), Seq.empty, Seq.empty, tpe, body, flags ++ Seq(Ghost, IsMethodOf(cd.id))).copiedFrom(cd)
    }

    // The copies of the identities of outer instances, see `hasGenericOuter`
    val outerIdentityAccessorDefs = symbols.classes.values.toSeq.filter(cd => hasGenericOuter(cd.id)).map { cd =>
      val ct = ClassType(cd.id, cd.typeArgs).copiedFrom(cd)
      val tpe = IntegerType().copiedFrom(cd)
      val (body, flags) =
        if (isAbstract(cd.id)) (NoTree(tpe).copiedFrom(cd), Seq(IsAbstract))
        else (ClassSelector(This(ct).copiedFrom(cd), outerIdentityFieldId(cd.id)).copiedFrom(cd), Seq(IsAccessor(Some(outerIdentityFieldId(cd.id)))))
      new FunDef(outerIdentityAccessorId(cd.id), Seq.empty, Seq.empty, tpe, body, flags ++ Seq(Ghost, IsMethodOf(cd.id))).copiedFrom(cd)
    }

    val classes = symbols.classes.values.map { cd =>
      val field = if (hasIdentityField(cd.id)) Some(ValDef(identityFieldId(cd.id), IntegerType().copiedFrom(cd), Seq(Ghost)).copiedFrom(cd)) else None
      // The outer instance comes first (see [[MemberClasses]])
      val fields =
        if (!hasOuterIdentityField(cd.id)) cd.fields
        else cd.fields.head +: ValDef(outerIdentityFieldId(cd.id), IntegerType().copiedFrom(cd), Seq(Ghost)).copiedFrom(cd) +: cd.fields.tail
      transformer.transform(cd.copy(fields = field.toSeq ++ fields).copiedFrom(cd))
    }

    NoSymbols
      .withFunctions((symbols.functions.values.toSeq ++ accessors ++ outerIdentityAccessorDefs).map(transformer.transform))
      .withSorts(symbols.sorts.values.toSeq)
      .withClasses(classes.toSeq)
      .withTypeDefs(symbols.typeDefs.values.map(transformer.transform).toSeq)
  }

  /** A placeholder for the identity of a new instance, drawn from the allocator below. */
  private def freshIdentity(pos: Expr): Expr =
    Annotated(NoTree(IntegerType()).copiedFrom(pos), Seq(Annotation("freshIdentity", Seq.empty))).copiedFrom(pos)

  override def extract(symbols0: s.Symbols): (t.Symbols, ExtractionSummary) = {
    val symbols = addIdentities(symbols0)
    val allocating0 = symbols.functions.values.filter(fd => exprOps.exists(isFreshIdentity)(fd.fullBody)).map(_.id).toSet
    if (allocating0.isEmpty) return (symbols, ExtractionSummary.NoSummary)

    // Overriding methods share their symbol, and must all take the allocator if one of them does
    val overrides: Map[Identifier, Set[Identifier]] = {
      val bySymbol = symbols.functions.keys.toSeq.collect { case id: SymbolIdentifier => id }.groupBy(_.symbol)
      symbols.functions.keys.map {
        case id: SymbolIdentifier if symbols.functions(id).isMethod => id -> bySymbol(id.symbol).toSet
        case id => id -> Set(id)
      }.toMap
    }

    val calls: Map[Identifier, Set[Identifier]] = symbols.functions.values.map(fd => fd.id -> callees(fd)).toMap

    var allocating = allocating0.flatMap(overrides)
    var changed = true
    while (changed) {
      val next = allocating ++ symbols.functions.keys.filter(id => calls(id).exists(allocating)).flatMap(overrides)
      changed = next.size != allocating.size
      allocating = next
    }

    val allocatorType = ClassType(allocatorId, Seq.empty)
    val allocator = new ClassDef(allocatorId, Seq.empty, Seq.empty, Seq(VarDef(nextId, IntegerType(), Seq(Ghost))), Seq.empty)

    def transform(fd: FunDef): FunDef = {
      val alloc = ValDef.fresh("alloc", allocatorType).copy(flags = Seq(Ghost)).copiedFrom(fd)

      object transformer extends ConcreteOOSelfTreeTransformer(self.s, self.s) {
        private var inLambda = false

        private def checkContext(e: Expr): Unit =
          if (inLambda) context.reporter.fatalError(e.getPos,
            "Stainless does not support constructing instances of classes with member classes within lambdas")

        override def transform(e: Expr): Expr = e match {
          case _ if isFreshIdentity(e) =>
            checkContext(e)
            val id = ValDef.fresh("id", IntegerType()).copy(flags = Seq(Ghost)).copiedFrom(e)
            val sel = ClassSelector(alloc.toVariable, nextId).copiedFrom(e)
            val incr = FieldAssignment(alloc.toVariable, nextId, Plus(id.toVariable, IntegerLiteral(1)).copiedFrom(e)).copiedFrom(e)
            Let(id, sel, Block(Seq(Annotated(incr, Seq(Ghost)).copiedFrom(e)), id.toVariable).copiedFrom(e)).copiedFrom(e)

          case FunctionInvocation(id, tps, args) if allocating(id) =>
            checkContext(e)
            FunctionInvocation(id, tps.map(transform), args.map(transform) :+ alloc.toVariable).copiedFrom(e)

          case MethodInvocation(rec, id, tps, args) if allocating(id) =>
            checkContext(e)
            MethodInvocation(transform(rec), id, tps.map(transform), args.map(transform) :+ alloc.toVariable).copiedFrom(e)

          case l: Lambda =>
            val old = inLambda
            inLambda = true
            try super.transform(l) finally inLambda = old

          case _ => super.transform(e)
        }
      }

      fd.copy(params = fd.params :+ alloc, fullBody = transformer.transform(fd.fullBody))
    }

    val newSymbols = NoSymbols
      .withFunctions(symbols.functions.values.map(fd => if (allocating(fd.id)) transform(fd) else fd).toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withClasses(symbols.classes.values.toSeq :+ allocator)
      .withTypeDefs(symbols.typeDefs.values.toSeq)

    (newSymbols, ExtractionSummary.NoSummary)
  }
}

object OuterIdentities {
  def apply(trees: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends OuterIdentities(s)(t)
    new Impl(trees, trees)
  }
}
