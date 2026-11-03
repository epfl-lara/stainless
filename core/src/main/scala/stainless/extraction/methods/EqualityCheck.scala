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
 *  rejects the programs in which an equality may compare values of type `Any`:
 *
 *    - `==`, literal patterns, the elements of `Set` and `Bag` and the keys of
 *      `Map` cannot involve a type that reaches `Any`, be it directly or
 *      through the fields of a class and of its descendants, tuple components
 *      or collection elements;
 *    - a type parameter whose values reach such an equality is
 *      equality-sensitive, and so is a type parameter of a class whose methods
 *      or structural equality compare its values. An equality-sensitive type
 *      parameter cannot be instantiated with a type that reaches `Any`;
 *    - an abstract type member whose values are compared cannot be defined as a
 *      type that reaches `Any` in a subclass. As the frontend dealiases the
 *      definitions of type members, these are found in the signatures of the
 *      methods overriding the ones that mention the member.
 *
 *  Which type parameters and members are compared is inferred by a
 *  whole-program analysis, a fixpoint over all definitions, rather than
 *  declared through an equality type class such as Scala 3's `CanEqual` or one
 *  of the Stainless library. The reason attached to each marking names the
 *  comparison it comes from, which may be in another function or in the
 *  library.
 *
 *  Wildcard type arguments (`C[?]`) are accepted: no value of such a type can
 *  be named, so the values compared inside `C` are the ones of the concrete
 *  type argument used to build the object, which is checked where it occurs.
 *
 *  The phase runs before [[Laws]] and [[MethodLifting]], while classes still
 *  own their methods and type arguments are the ones written by the user. All
 *  errors are reported and [[ExtractionFailed]] is thrown if there is at least
 *  one.
 *
 *  Implementation: `reach` lists the leaf types that structural equality on a
 *  type visits (through the fields of the classes it mentions and of their
 *  descendants, tuple components and collection elements) and the classes it
 *  goes through. `compared` records that values of a type are compared: it
 *  reports an error for each `Any` leaf, marks the type parameters among the
 *  leaves as equality-sensitive (`sensitive`, keyed by the declaring function
 *  or class and the index), marks the abstract type members among them
 *  (`sensitiveMembers`), and marks the classes gone through as structurally
 *  compared (`markStructural`), which makes the type parameters of these
 *  classes and of their descendants sensitive too. The traverser calls
 *  `compared` on the type of each `==` and literal pattern (`comparedType`, the
 *  least upper bound with pairwise type arguments), on the element and key
 *  types of collections (`occurrence`), and on the arguments passed for
 *  sensitive type parameters at each call (`instantiation`) and in each class
 *  type (`occurrence`). `propagateToParents` marks the parameters of parent
 *  classes instantiated by sensitive ones, and `checkMembers` finds the
 *  definitions of sensitive type members in the signatures of overriding
 *  methods. `check` repeats these passes until no type parameter or member is
 *  newly marked, then runs a last pass that reports the errors.
 *
 *  @see
 *    https://github.com/epfl-lara/stainless/issues/1821
 */
class EqualityCheck(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
    extends ExtractionPipeline:
  self =>

  import s.*

  override def invalidate(id: Identifier): Unit = ()

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) =
    new Checker(symbols).check()
    (symbols, ExtractionSummary.NoSummary)

  private class Checker(val symbols: s.Symbols):
    import symbols.{*, given}

    private given PrinterOptions = PrinterOptions.fromSymbols(symbols, context)

    /** A type parameter is identified by the function or class declaring it and
     *  its index.
     */
    private type Owner = (Identifier, Int)

    private val localFunDefs: Seq[LocalFunDef] = symbols.functions.values.toSeq.flatMap { fd =>
      exprOps.collect[LocalFunDef] {
        case LetRec(fds, _) => fds.toSet
        case _ => Set.empty
      }(fd.fullBody)
    }

    private val funTypeParams: Map[Identifier, Seq[TypeParameter]] =
      symbols.functions.values.map(fd => fd.id -> fd.typeArgs).toMap ++
        localFunDefs.map(lfd => lfd.id -> lfd.tparams.map(_.tp))

    private val tparamOwners: Map[Identifier, Owner] =
      val funs = funTypeParams.toSeq.flatMap { case (id, tps) =>
        tps.zipWithIndex.map { case (tp, i) => tp.id -> (id, i) }
      }
      val classes = symbols.classes.values.toSeq.flatMap { cd =>
        cd.typeArgs.zipWithIndex.map { case (tp, i) => tp.id -> (cd.id, i) }
      }
      (funs ++ classes).toMap

    /** Equality-sensitive type parameters, with the reason why they are. */
    private val sensitive = mutable.Map.empty[Owner, String]

    /** Abstract type members whose values are compared, with the reason why. */
    private val sensitiveMembers = mutable.Map.empty[Identifier, String]

    /** Classes whose values are compared structurally. */
    private val structural = mutable.Set.empty[Identifier]

    private var changed = false
    private var reporting = false
    private val errors = mutable.LinkedHashSet.empty[(Position, String)]

    /** The definition being traversed, for the name in reasons and the position
     *  of errors on trees without a position.
     */
    private var currentName: String = ""
    private var currentPos: Position = NoPosition

    private def inDefinition[A](name: String, pos: Position)(body: => A): A =
      val (savedName, savedPos) = (currentName, currentPos)
      currentName = name
      currentPos = pos
      try body
      finally
        currentName = savedName
        currentPos = savedPos

    private def definitionName(fd: FunDef): String = fd.getClassId match
      case Some(cid) => s"${cid.name}.${fd.id.name}"
      case None => fd.id.name

    private def report(site: Tree, msg: String): Unit = if reporting then
      val pos = if site.getPos != NoPosition then site.getPos else currentPos
      errors += ((pos, msg))

    private def mark(owner: Owner, reason: String): Unit = if !sensitive.contains(owner) then
      sensitive(owner) = reason
      changed = true

    private def markMember(td: TypeDef, reason: String): Unit =
      if td.isAbstract && !sensitiveMembers.contains(td.id) then
        sensitiveMembers(td.id) = reason
        changed = true

    /** The type definition applied by a [[TypeApply]], if it can be found. */
    private def typeDefOf(ta: TypeApply): Option[TypeDef] =
      scala.util.Try(ta.lookupTypeDef).toOption.flatten.filter(_.tparams.size == ta.tps.size)

    private def anyClause(where: Option[String]): String = where match
      case None => "equality on `Any` is not supported"
      case Some(where) => s"$where may be of type `Any`, and equality on `Any` is not supported"

    /* ====================================
     *      TYPES REACHED BY EQUALITY
     * ==================================== */

    /** The leaf types reached from a type by structural equality, each with a
     *  description of where it lies (`None` for the type itself), and the class
     *  types traversed on the way.
     */
    private case class Reach(leaves: Seq[(Type, Option[String])], classes: Seq[ClassType])

    private val reachCache = mutable.Map.empty[Type, Reach]

    private def reach(tpe: Type): Reach = reachCache.getOrElseUpdate(
      tpe, {
        val seen = mutable.Set.empty[Type]
        val leaves = mutable.ListBuffer.empty[(Type, Option[String])]
        val classes = mutable.ListBuffer.empty[ClassType]

        def go(tpe: Type, where: Option[String]): Unit = if seen.add(tpe) then
          tpe match
            case ct: ClassType =>
              classes += ct
              ct.lookupClass.foreach { tcd =>
                (tcd +: tcd.descendants).foreach { d =>
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
        Reach(leaves.toSeq, classes.toSeq)
      }
    )

    /** Records that values of type `tpe` are compared with `==` for `reason`:
     *  marks the type parameters and type members it reaches as
     *  equality-sensitive and the classes it reaches as structurally compared,
     *  and reports an error built by `error` at `site` if it reaches `Any`.
     *  Returns whether an error was found.
     */
    private def compared(tpe: Type, reason: String, error: Option[String] => String, site: Tree): Boolean =
      val Reach(leaves, classes) = reach(tpe)
      classes.foreach(markStructural(_, reason))
      leaves.map {
        case (AnyType(), where) =>
          report(site, error(where))
          true
        case (tp: TypeParameter, _) =>
          tparamOwners.get(tp.id).foreach(mark(_, reason))
          false
        case (ta: TypeApply, _) =>
          typeDefOf(ta).foreach(markMember(_, reason))
          false
        case _ => false
      }.exists(identity)

    /** Marks the type parameters of `ct` and of its descendants whose values
     *  are compared when values of `ct` are compared structurally.
     */
    private def markStructural(ct: ClassType, reason: String): Unit = if structural.add(ct.id) then
      lookupClass(ct.id).foreach { cd =>
        (cd +: cd.descendants).foreach { d =>
          val reached = d.fields.map(vd => reach(vd.tpe))
          val tparams = reached.flatMap(_.leaves).collect { case (tp: TypeParameter, _) => tp.id }.toSet
          d.typeArgs.zipWithIndex.foreach { case (tp, i) =>
            if tparams(tp.id) then mark((d.id, i), reason)
          }
          reached.flatMap(_.classes).foreach(markStructural(_, reason))
        }
      }

    /* ====================================
     *            TRAVERSAL
     * ==================================== */

    private def tparamName(owner: Owner): String =
      val (id, i) = owner
      funTypeParams.get(id).map(_(i)).getOrElse(symbols.getClass(id).typeArgs(i)).id.name

    private def widen(tpe: Type): Type = tpe match
      case tp: TypeParameter => widen(tp.upperBound)
      case ta: TypeApply => widen(ta.upperBound)
      case _ => tpe

    /** Checks the type arguments passed for the equality-sensitive type
     *  parameters of `id`.
     */
    private def instantiation(id: Identifier, tps: Seq[Type], site: Tree): Unit =
      tps.zipWithIndex.foreach { case (arg, i) =>
        sensitive.get((id, i)).foreach { reason =>
          arg match
            case TypeBounds(_, _, _) => ()
            case _ => compared(
                arg,
                reason,
                where =>
                  s"Cannot call `${id.name}` with the type argument `${arg.asString}`: " +
                    s"values of its type parameter `${tparamName((id, i))}` are compared with `==` $reason, " +
                    s"and ${anyClause(where)}",
                site
              )
        }
      }

    /** Checks a type occurring in the program. Returns whether an error was
     *  found.
     */
    private def occurrence(tpe: Type): Boolean = tpe match
      case ct @ ClassType(id, tps) =>
        tps.zipWithIndex.map { case (arg, i) =>
          sensitive.get((id, i)) match
            case Some(reason) => arg match
                case TypeBounds(_, _, _) => false
                case _ => compared(
                    arg,
                    reason,
                    where =>
                      s"Cannot use the type `${ct.asString}`: " +
                        s"values of its type parameter `${tparamName((id, i))}` are compared with `==` $reason, " +
                        s"and ${anyClause(where)}",
                    ct
                  )
            case None => false
        }.exists(identity)

      case SetType(base) => collection(tpe, "Set", base, "elements")
      case BagType(base) => collection(tpe, "Bag", base, "elements")
      case MapType(from, _) => collection(tpe, "Map", from, "keys")
      case MutableMapType(from, _) => collection(tpe, "MutableMap", from, "keys")
      case _ => false

    private def collection(tpe: Type, kind: String, key: Type, what: String): Boolean =
      compared(
        key,
        s"(as $what of a `$kind`)",
        where =>
          s"Cannot use a `$kind` with $what of type `${key.asString}`: $what are compared with `==`, and ${anyClause(where)}",
        tpe
      )

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
        val types = if lt == rt then s"values of type `${lt.asString}`"
        else s"values of type `${lt.asString}` and `${rt.asString}`"
        compared(lub, s"(in `$currentName`)", where => s"Cannot compare $types with `==`: ${anyClause(where)}", site)

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
        if !occurrence(tpe) then super.traverse(tpe)

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
              compared(
                lub,
                s"(in `$currentName`)",
                where =>
                  s"Cannot match a value of type `${in.asString}` against the literal `${lit.asString}` of type `${lit.getType.asString}`: ${anyClause(where)}",
                site
              )

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
     *          WHOLE-PROGRAM PASSES
     * ==================================== */

    private def ordered[A <: Tree](defs: Iterable[A], name: A => String): Seq[A] =
      defs.toSeq.sortBy(d => (d.getPos, name(d)))

    private val functions = ordered(symbols.functions.values, (fd: FunDef) => fd.id.name)
    private val classes = ordered(symbols.classes.values, (cd: ClassDef) => cd.id.name)
    private val typeDefs = ordered(symbols.typeDefs.values, (td: TypeDef) => td.id.name)

    /** Propagates the equality-sensitivity of the type parameters of a class to
     *  the parameters of its parents they instantiate, as a parent-typed value
     *  may be an instance of the class.
     */
    private def propagateToParents(): Unit = classes.foreach { cd =>
      cd.typeArgs.zipWithIndex.foreach { case (tp, j) =>
        sensitive.get((cd.id, j)).foreach { reason =>
          cd.parents.foreach { parent =>
            parent.tps.zipWithIndex.foreach { case (arg, k) =>
              if reach(arg).leaves.exists { case (tp2: TypeParameter, _) => tp2.id == tp.id; case _ => false } then
                mark((parent.id, k), reason)
            }
          }
        }
      }
    }

    /** The methods overriding each method, transitively. */
    private val overriders: Map[Identifier, Seq[FunDef]] =
      val pairs = functions.filter(_.isMethod).flatMap { fd =>
        val first = firstSuperMethod(fd.id.asInstanceOf[stainless.ast.SymbolIdentifier])
        Iterator.unfold(first)(_.map(sid => (sid, firstSuperMethod(sid)))).map(sid => (sid: Identifier) -> fd).toSeq
      }
      pairs.groupMap(_._1)(_._2)

    /** Checks the definitions of the abstract type members whose values are
     *  compared. The definition of a member `M` in a subclass is visible in the
     *  signature of a method overriding a method of the declaring class that
     *  mentions `this.M`.
     */
    private def checkMembers(): Unit = sensitiveMembers.toSeq.sortBy(_._1.name).foreach { case (tdId, reason) =>
      for
        fd <- functions
        overrider <- overriders.getOrElse(fd.id, Seq.empty)
        if overrider.params.size == fd.params.size
      do
        inDefinition(definitionName(overrider), overrider.getPos) {
          ((fd.params.map(_.tpe) :+ fd.returnType) zip (overrider.params.map(_.tpe) :+ overrider.returnType)).foreach {
            case (declared, overriding) => memberDefinition(tdId, reason, declared, overriding, overrider)
          }
        }
    }

    /** Finds the definitions of the type member `tdId` by matching the type
     *  `declared` of a method of its declaring class against the type
     *  `overriding` of an overriding method.
     */
    private def memberDefinition(tdId: Identifier, reason: String, declared: Type, overriding: Type, site: Tree): Unit =
      (declared, overriding) match
        case (TypeApply(TypeSelect(_, selector), Seq()), _) if selector == tdId =>
          overriding match
            case TypeApply(TypeSelect(_, selector2), Seq()) if selector2 == tdId => ()
            case _ => compared(
                overriding,
                reason,
                where =>
                  s"Cannot define the type member `${tdId.name}` as `${overriding.asString}`: " +
                    s"values of type `${tdId.name}` are compared with `==` $reason, and ${anyClause(where)}",
                site
              )
        case (NAryType(dtps, _), NAryType(otps, _)) if dtps.size == otps.size =>
          (dtps zip otps).foreach { case (d, o) => memberDefinition(tdId, reason, d, o, site) }
        case _ => ()

    private def pass(): Unit =
      functions.foreach(fd => inDefinition(definitionName(fd), fd.getPos)(traverser.traverse(fd)))
      classes.foreach(cd => inDefinition(cd.id.name, cd.getPos)(traverser.traverse(cd)))
      typeDefs.foreach(td => inDefinition(td.id.name, td.getPos)(traverser.traverse(td)))
      propagateToParents()
      checkMembers()

    def check(): Unit =
      while { changed = false; pass(); changed } do ()
      reporting = true
      pass()
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
