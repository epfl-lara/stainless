/* Copyright 2009-2025 EPFL, Lausanne */

package stainless
package extraction
package methods

import scala.collection.mutable

import inox.utils.{NoPosition, Position}

/** Rejects equalities whose runtime semantics are not modelled by Stainless.
 *
 *  On the JVM, `==` between two values of static type `Any` compares boxed
 *  numbers by value across numeric types, and compares boxed floating-point
 *  numbers with IEEE semantics:
 *
 *  ```
 *  val a: Any = (5: Byte)
 *  val b: Any = 5
 *  a == b // true on the JVM
 *  ```
 *
 *  The type encoding gives `Any` a structural equality in which values of
 *  different types are never equal, so it would prove `a != b`. This phase
 *  rejects the programs in which an equality may compare values of type `Any`.
 *
 *  Every type parameter and abstract type member is an equality type unless it
 *  is annotated `@noeq`: values of an equality type can be compared with `==`,
 *  and in exchange it can only be instantiated with types on which `==` is
 *  sound, which are the types that do not reach `Any` or a `@noeq` type
 *  parameter or member, directly or through the fields of a class and of its
 *  descendants, tuple components or collection elements. The rules are:
 *
 *    - `==`, literal patterns, the elements of `Set` and `Bag` and the keys of
 *      `Map` cannot involve a type that reaches `Any` or a `@noeq` type
 *      parameter or member;
 *    - the type argument passed for an equality type parameter, in a call, in a
 *      class type or in the parents of a class, cannot reach `Any` or a `@noeq`
 *      type parameter or member;
 *    - an abstract type member that is an equality type cannot be defined as
 *      such a type in a subclass. As the frontend dealiases the definitions of
 *      type members, these are found in the signatures of the methods
 *      overriding the ones that mention the member;
 *    - a method overriding a method with a `@noeq` type parameter must annotate
 *      the parameter `@noeq` as well, as it may be called at that type.
 *
 *  Two more equalities are rejected for the same reason, a disagreement with
 *  the JVM (https://github.com/epfl-lara/stainless/issues/1483): the values of
 *  a class that is not a case class are compared by reference on the JVM, so
 *  such a class is treated like `Any` above, and a class cannot override
 *  `equals`.
 *
 *  This mirrors how `@mutable` lets a type parameter be instantiated with
 *  mutable types, and as `Any` is also a mutable type for Stainless, a type
 *  parameter needs both annotations to be instantiated with `Any`. Wildcard
 *  type arguments (`C[?]`) are accepted: no value of such a type can be named,
 *  so the values compared inside `C` are the ones of the concrete type argument
 *  used to build the object, which is checked where it occurs.
 *
 *  The phase runs before [[Laws]] and [[MethodLifting]], while classes still
 *  own their methods and type arguments are the ones written by the user. All
 *  errors are reported and [[ExtractionFailed]] is thrown if there is at least
 *  one.
 *
 *  Implementation: `reach` lists the leaf types that structural equality on a
 *  type visits, and `unsafe` describes the first of them that is `Any` or a
 *  `@noeq` type parameter or member, if any. The traverser applies `unsafe` to
 *  the type of each `==` and literal pattern (`comparedType`, the least upper
 *  bound with pairwise type arguments), to the element and key types of
 *  collections, and to the arguments passed for equality type parameters at
 *  each call (`instantiation`) and in each class type (`occurrence`).
 *  `checkMembers` finds the definitions of the abstract type members in the
 *  signatures of overriding methods, and `checkOverrides` compares the
 *  annotations of overriding methods.
 *
 *  @see
 *    https://github.com/epfl-lara/stainless/issues/1821
 *  @see
 *    https://github.com/epfl-lara/stainless/issues/1483
 */
class EqualityCheck(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
    extends ExtractionPipeline:
  self =>

  import s.*

  override def invalidate(id: Identifier): Unit = ()

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) =
    new Checker(symbols).check()
    (stripNoEq(symbols), ExtractionSummary.NoSummary)

  /** Removes the `@noeq` annotations and the [[IsPlainClass]] flags, which have
   *  no meaning after this phase.
   */
  private def stripNoEq(symbols: s.Symbols): t.Symbols =
    val stripper = new self.s.ConcreteOOSelfTreeTransformer(self.s, self.s):
      override def transform(tpe: self.s.Type): self.s.Type = tpe match
        case tp @ self.s.TypeParameter(id, flags) if flags contains NoEq =>
          self.s.TypeParameter(id, flags.filterNot(_ == NoEq).map(transform)).copiedFrom(tp)
        case _ => super.transform(tpe)

      override def transform(td: self.s.TypeDef): self.s.TypeDef =
        val ntd = super.transform(td)
        new self.s.TypeDef(ntd.id, ntd.tparams, ntd.rhs, ntd.flags.filterNot(_ == NoEq)).copiedFrom(td)

      override def transform(cd: self.s.ClassDef): self.s.ClassDef =
        val ncd = super.transform(cd)
        new self.s.ClassDef(ncd.id, ncd.tparams, ncd.parents, ncd.fields, ncd.flags.filterNot(_ == IsPlainClass))
          .copiedFrom(cd)

    t.NoSymbols
      .withFunctions(symbols.functions.values.toSeq.map(stripper.transform))
      .withSorts(symbols.sorts.values.toSeq.map(stripper.transform))
      .withClasses(symbols.classes.values.toSeq.map(stripper.transform))
      .withTypeDefs(symbols.typeDefs.values.toSeq.map(stripper.transform))

  private class Checker(val symbols: s.Symbols):
    import symbols.{*, given}

    private given PrinterOptions = PrinterOptions.fromSymbols(symbols, context)

    private val localFunDefs: Seq[LocalFunDef] = symbols.functions.values.toSeq.flatMap { fd =>
      exprOps.collect[LocalFunDef] {
        case LetRec(fds, _) => fds.toSet
        case _ => Set.empty
      }(fd.fullBody)
    }

    /** The type parameters declared by each function, local functions included.
     */
    private val funTypeParams: Map[Identifier, Seq[TypeParameter]] =
      symbols.functions.values.map(fd => fd.id -> fd.typeArgs).toMap ++
        localFunDefs.map(lfd => lfd.id -> lfd.tparams.map(_.tp))

    private val errors = mutable.LinkedHashSet.empty[(Position, String)]

    /** The position of the definition being traversed, for errors on trees
     *  without a position.
     */
    private var currentPos: Position = NoPosition

    private def inDefinition[A](pos: Position)(body: => A): A =
      val savedPos = currentPos
      currentPos = pos
      try body
      finally currentPos = savedPos

    private def report(site: Tree, msg: String): Unit =
      val pos = if site.getPos != NoPosition then site.getPos else currentPos
      errors += ((pos, msg))

    private def isNoEq(flags: Seq[Flag]): Boolean = flags contains NoEq

    /** The type definition applied by a [[TypeApply]], if it can be found. */
    private def typeDefOf(ta: TypeApply): Option[TypeDef] =
      scala.util.Try(ta.lookupTypeDef).toOption.flatten.filter(_.tparams.size == ta.tps.size)

    /* ====================================
     *      TYPES REACHED BY EQUALITY
     * ==================================== */

    private val reachCache = mutable.Map.empty[Type, Seq[(Type, Option[String])]]

    /** The leaf types reached from a type by structural equality, each with a
     *  description of where it lies (`None` for the type itself).
     */
    private def reach(tpe: Type): Seq[(Type, Option[String])] = reachCache.getOrElseUpdate(
      tpe, {
        val seen = mutable.Set.empty[Type]
        val leaves = mutable.ListBuffer.empty[(Type, Option[String])]

        def go(tpe: Type, where: Option[String]): Unit = if seen.add(tpe) then
          tpe match
            case ct: ClassType =>
              // Heap references of the full imperative mode are compared by identity, not by their fields
              ct.lookupClass.filterNot(isHeapRef).foreach { tcd =>
                (tcd +: tcd.descendants).foreach { d =>
                  if isPlain(d) then leaves += ((d.toType, where))
                  d.fields.foreach { vd =>
                    go(vd.tpe, Some(s"the field `${vd.id.name}` of `${d.toType.asString}`"))
                  }
                }
              }
            case ADTType(id, tps) =>
              lookupSort(id).foreach { sort =>
                sort.typed(tps).constructors.foreach { cons =>
                  cons.fields.foreach { vd =>
                    go(vd.tpe, Some(s"the field `${vd.id.name}` of `${cons.id.name}`"))
                  }
                }
              }
            case TupleType(tps) =>
              tps.zipWithIndex.foreach { case (tp, i) =>
                go(tp, Some(s"the component ${i + 1} of `${tpe.asString}`"))
              }
            case SetType(base) => go(base, Some(s"the elements of `${tpe.asString}`"))
            case BagType(base) => go(base, Some(s"the elements of `${tpe.asString}`"))
            case ArrayType(base) => go(base, Some(s"the elements of `${tpe.asString}`"))
            case MapType(from, to) =>
              go(from, Some(s"the keys of `${tpe.asString}`"))
              go(to, Some(s"the values of `${tpe.asString}`"))
            case MutableMapType(from, to) =>
              go(from, Some(s"the keys of `${tpe.asString}`"))
              go(to, Some(s"the values of `${tpe.asString}`"))
            case RefinementType(vd, _) => go(vd.tpe, where)
            case pi: PiType => go(pi.getType, where)
            case sigma: SigmaType => go(sigma.getType, where)
            case FunctionType(_, _) => ()
            case ta: TypeApply if typeDefOf(ta).exists(!_.isAbstract) => go(ta.resolve, where)
            case other => leaves += ((other, where))

        go(tpe, None)
        leaves.toSeq
      }
    )

    /** Is `tcd` a heap reference of the full imperative mode? Their identity is
     *  modelled, so they are compared soundly whatever their fields.
     */
    private def isHeapRef(tcd: TypedClassDef): Boolean =
      (tcd +: tcd.ancestors).exists(_.cd.flags.exists(_.name == "anyHeapRef"))

    /** Is `tcd` a class whose values are compared by reference on the JVM? */
    private def isPlain(tcd: TypedClassDef): Boolean = (tcd.cd.flags contains IsPlainClass) && !isHeapRef(tcd)

    /** Why `==` on values of type `tpe` is not supported, if it is not: the
     *  first `Any`, class compared by reference, `@noeq` type parameter or
     *  `@noeq` type member reached.
     */
    private def unsafe(tpe: Type): Option[String] = reach(tpe).view.flatMap {
      case (AnyType(), where) =>
        Some(where.fold("equality on `Any` is not supported")(w =>
          s"$w may be of type `Any`, and equality on `Any` is not supported"
        ))
      case (ct: ClassType, where) =>
        val name = s"`${ct.id.name}`"
        Some(where.fold(s"$name is not a case class, so its values are compared by reference on the JVM")(w =>
          s"$w may be a $name, which is not a case class, so its values are compared by reference on the JVM"
        ))
      case (tp: TypeParameter, where) if isNoEq(tp.flags) =>
        val name = s"`${tp.id.name}`"
        Some(where.fold(s"the type parameter $name is annotated `@noeq`")(w =>
          s"$w is of type $name, a type parameter annotated `@noeq`"
        ))
      case (ta: TypeApply, where) if typeDefOf(ta).exists(td => isNoEq(td.flags)) =>
        val name = s"`${typeDefOf(ta).get.id.name}`"
        Some(where.fold(s"the type member $name is annotated `@noeq`")(w =>
          s"$w is of type $name, a type member annotated `@noeq`"
        ))
      case _ => None
    }.headOption

    /* ====================================
     *            TRAVERSAL
     * ==================================== */

    private def widen(tpe: Type): Type = tpe match
      case tp: TypeParameter => widen(tp.upperBound)
      case ta: TypeApply => widen(ta.upperBound)
      case _ => tpe

    /** Checks the type arguments `tps` passed for the type parameters `tparams`
     *  of `id`.
     */
    private def arguments(id: Identifier, tparams: Seq[TypeParameter], tps: Seq[Type], site: Tree, use: String): Unit =
      (tparams zip tps).foreach { case (tp, arg) =>
        if !isNoEq(tp.flags) then
          arg match
            case TypeBounds(_, _, _) => ()
            case _ => unsafe(arg).foreach { why =>
                report(
                  site,
                  s"Cannot $use: $why, and the type parameter `${tp.id.name}` of `${id.name}` is not annotated `@noeq`"
                )
              }
      }

    /** Checks the type arguments of a call to `id`. */
    private def instantiation(id: Identifier, tps: Seq[Type], site: Tree): Unit =
      funTypeParams.get(id).foreach { tparams =>
        arguments(
          id,
          tparams,
          tps,
          site,
          s"call `${id.name}` with the type argument${if tps.size > 1 then "s" else ""} ${tps.map(tp => s"`${tp.asString}`").mkString(", ")}"
        )
      }

    /** Checks a type occurring in the program. */
    private def occurrence(tpe: Type): Unit = tpe match
      case ct @ ClassType(id, tps) =>
        ct.lookupClass.foreach(tcd => arguments(id, tcd.cd.typeArgs, tps, ct, s"use the type `${ct.asString}`"))
      case SetType(base) => collection(tpe, "Set", base, "elements")
      case BagType(base) => collection(tpe, "Bag", base, "elements")
      case MapType(from, _) => collection(tpe, "Map", from, "keys")
      case MutableMapType(from, _) => collection(tpe, "MutableMap", from, "keys")
      case _ => ()

    private def collection(tpe: Type, kind: String, key: Type, what: String): Unit =
      unsafe(key).foreach { why =>
        report(
          tpe,
          s"Cannot use a `$kind` with $what of type `${key.asString}`: $what are compared with `==`, and $why"
        )
      }

    /** The type at which values of types `t1` and `t2` are compared. This is
     *  their least upper bound, except that the type arguments of a common
     *  class are compared pairwise even where the class is invariant
     *  (`List[IntCell] == List[AnyHeapRef]` compares `IntCell` and `AnyHeapRef`
     *  values, not values of type `Any`).
     */
    private def comparedType(t1: Type, t2: Type): Type = leastUpperBound(t1, t2) match
      case AnyType() => (t1, t2) match
          case (ct1: ClassType, ct2: ClassType) =>
            val common =
              for
                tcd1 <- ct1.lookupClass.toSeq
                tcd2 <- ct2.lookupClass.toSeq
                a1 <- tcd1 +: tcd1.ancestors
                a2 <- (tcd2 +: tcd2.ancestors).find(_.id == a1.id).toSeq
              yield ClassType(a1.id, (a1.tps zip a2.tps).map(comparedType))
            common.headOption.getOrElse(AnyType())
          case (ADTType(id1, tps1), ADTType(id2, tps2)) if id1 == id2 && tps1.size == tps2.size =>
            ADTType(id1, (tps1 zip tps2).map(comparedType))
          case (SetType(b1), SetType(b2)) => SetType(comparedType(b1, b2))
          case (BagType(b1), BagType(b2)) => BagType(comparedType(b1, b2))
          case (MapType(k1, v1), MapType(k2, v2)) => MapType(comparedType(k1, k2), comparedType(v1, v2))
          case _ => AnyType()
      case lub => lub

    private def equality(lhs: Expr, rhs: Expr, site: Expr): Unit =
      val (lt, rt) = (lhs.getType, rhs.getType)
      val lub = comparedType(lt, rt)
      if lub != Untyped then
        unsafe(lub).foreach { why =>
          val types = if lt == rt then s"values of type `${lt.asString}`"
          else s"values of type `${lt.asString}` and `${rt.asString}`"
          report(site, s"Cannot compare $types with `==`: $why")
        }

    private object traverser extends s.ConcreteOOSelfTreeTraverser:
      override def traverse(e: Expr): Unit = e match
        case Equals(lhs, rhs) =>
          equality(lhs, rhs, e)
          super.traverse(e)

        case MatchExpr(scrut, cases) =>
          traverse(scrut)
          cases.foreach { case mc @ MatchCase(pat, guard, rhs) =>
            traversePattern(pat, scrut.getType, if mc.getPos != NoPosition then mc else e)
            guard.foreach(traverse)
            traverse(rhs)
          }

        case FunInvocation(id, tps, _, _) =>
          instantiation(id, tps, e)
          super.traverse(e)

        case MethodInvocation(_, id, tps, _) =>
          instantiation(id, tps, e)
          super.traverse(e)

        case _ => super.traverse(e)

      override def traverse(tpe: Type): Unit =
        occurrence(tpe)
        super.traverse(tpe)

      /** Traverses a pattern matched against a value of type `in`; `fallback`
       *  gives the position of errors on patterns without a position.
       */
      def traversePattern(pat: Pattern, in: Type, fallback: Tree): Unit =
        pat.binder.foreach(traverse)
        val site = if pat.getPos != NoPosition then pat else fallback
        pat match
          case WildcardPattern(_) => ()

          case LiteralPattern(_, lit) =>
            val lub = comparedType(lit.getType, in)
            if lub != Untyped then
              unsafe(lub).foreach { why =>
                report(
                  site,
                  s"Cannot match a value of type `${in.asString}` against the literal `${lit.asString}` of type `${lit.getType.asString}`: $why"
                )
              }

          case InstanceOfPattern(_, tpe) => traverse(tpe)

          case ClassPattern(_, ct, subs) =>
            traverse(ct)
            ct.lookupClass.foreach { tcd =>
              (subs zip tcd.fields).foreach { case (sub, vd) => traversePattern(sub, vd.getType, site) }
            }

          case ADTPattern(_, id, tps, subs) =>
            tps.foreach(traverse)
            lookupConstructor(id).foreach { cons =>
              (subs zip cons.typed(tps).fields).foreach { case (sub, vd) => traversePattern(sub, vd.getType, site) }
            }

          case TuplePattern(_, subs) => widen(in.getType) match
              case TupleType(tps) if tps.size == subs.size =>
                (subs zip tps).foreach { case (sub, tpe) => traversePattern(sub, tpe, site) }
              case _ =>
                subs.foreach(sub => traversePattern(sub, patternInType(sub), site))

          case AlternativePattern(_, subs) => subs.foreach(traversePattern(_, in, site))

          case RefinementPattern(sub, pred) =>
            traverse(pred)
            traversePattern(sub, in, site)

          case up @ UnapplyPattern(_, recs, id, tps, subs) =>
            recs.foreach(traverse)
            tps.foreach(traverse)
            instantiation(id, tps, site)
            (subs zip up.subTypes(in)).foreach { case (sub, tpe) => traversePattern(sub, tpe, site) }

    /* ====================================
     *       TYPE MEMBERS AND OVERRIDES
     * ==================================== */

    private def ordered[A <: Tree](defs: Iterable[A], name: A => String): Seq[A] =
      defs.toSeq.sortBy(d => (d.getPos, name(d)))

    private val functions = ordered(symbols.functions.values, (fd: FunDef) => fd.id.name)
    private val classes = ordered(symbols.classes.values, (cd: ClassDef) => cd.id.name)
    private val typeDefs = ordered(symbols.typeDefs.values, (td: TypeDef) => td.id.name)

    /** The first method overridden by each method, if any. */
    private val overridden: Map[Identifier, FunDef] = functions.flatMap { fd =>
      fd.id match
        case sid: stainless.ast.SymbolIdentifier if fd.isMethod =>
          firstSuperMethod(sid).flatMap(lookupFunction).map(fd.id -> _)
        case _ => None
    }.toMap

    /** The methods overriding each method, transitively. */
    private val overriders: Map[Identifier, Seq[FunDef]] =
      val pairs = functions.flatMap { fd =>
        Iterator.unfold(overridden.get(fd.id))(_.map(sfd => (sfd, overridden.get(sfd.id)))).map(sfd => sfd.id -> fd).toSeq
      }
      pairs.groupMap(_._1)(_._2)

    /** Checks the definitions of the abstract type members that are equality
     *  types. The definition of a member `M` in a subclass is visible in the
     *  signature of a method overriding a method of the declaring class that
     *  mentions `this.M`.
     */
    private def checkMembers(): Unit = typeDefs.filter(td => td.isAbstract && !isNoEq(td.flags)).foreach { td =>
      for
        fd <- functions
        overrider <- overriders.getOrElse(fd.id, Seq.empty)
        if overrider.params.size == fd.params.size
      do
        inDefinition(overrider.getPos) {
          ((fd.params.map(_.tpe) :+ fd.returnType) zip (overrider.params.map(_.tpe) :+ overrider.returnType)).foreach {
            case (declared, overriding) => memberDefinition(td, declared, overriding, overrider)
          }
        }
    }

    /** Finds the definitions of the type member `td` by matching the type
     *  `declared` of a method of its declaring class against the type
     *  `overriding` of an overriding method.
     */
    private def memberDefinition(td: TypeDef, declared: Type, overriding: Type, site: Tree): Unit =
      (declared, overriding) match
        case (TypeApply(TypeSelect(_, selector), Seq()), _) if selector == td.id =>
          overriding match
            case TypeApply(TypeSelect(_, selector2), Seq()) if selector2 == td.id => ()
            case _ => unsafe(overriding).foreach { why =>
                report(
                  site,
                  s"Cannot define the type member `${td.id.name}` as `${overriding.asString}`: $why, and `${td.id.name}` is not annotated `@noeq`"
                )
              }
        case (NAryType(dtps, _), NAryType(otps, _)) if dtps.size == otps.size =>
          (dtps zip otps).foreach { case (d, o) => memberDefinition(td, d, o, site) }
        case _ => ()

    /** Checks that a method overriding a method with a `@noeq` type parameter
     *  annotates it as well.
     */
    private def checkOverrides(): Unit = functions.foreach { fd =>
      overridden.get(fd.id).foreach { sfd =>
        (sfd.typeArgs zip fd.typeArgs).foreach { case (stp, tp) =>
          if isNoEq(stp.flags) && !isNoEq(tp.flags) then
            report(
              fd,
              s"The type parameter `${tp.id.name}` of `${fd.id.name}` must be annotated `@noeq`, as in the method it overrides"
            )
        }
      }
    }

    /** Rejects the methods overriding `equals`: `==` would not compare values
     *  structurally.
     */
    private def checkEquals(): Unit = functions.foreach { fd =>
      if fd.isMethod && fd.id.name == "equals" && fd.params.map(_.tpe) == Seq(AnyType()) then
        report(
          fd,
          s"Cannot override `equals` in `${fd.getClassId.fold("")(_.name)}`: Stainless compares values structurally"
        )
    }

    def check(): Unit =
      functions.foreach(fd => inDefinition(fd.getPos)(traverser.traverse(fd)))
      classes.foreach(cd => inDefinition(cd.getPos)(traverser.traverse(cd)))
      typeDefs.foreach(td => inDefinition(td.getPos)(traverser.traverse(td)))
      checkMembers()
      checkOverrides()
      checkEquals()
      if errors.nonEmpty then
        errors.toSeq.sortBy(_._1).foreach { case (pos, msg) => context.reporter.error(pos, msg) }
        throw ExtractionFailed()

object EqualityCheck:
  def apply(tr: Trees)(using inox.Context): ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } =
    class Impl(override val s: tr.type, override val t: tr.type) extends EqualityCheck(s)(t)
    new Impl(tr, tr)
