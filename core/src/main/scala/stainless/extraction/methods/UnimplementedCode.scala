/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package extraction
package methods

import java.util.IdentityHashMap

import stainless.ast.{Symbol, SymbolIdentifier}

/** Requires the missing implementations (`???`) of executable code to be unreachable.
  *
  * Scala throws a `NotImplementedError` when it evaluates `???`, whereas the following phases treat
  * it as an unknown value that satisfies the specification around it. This phase guards each `???`
  * that the program may evaluate with an `assert(false)`, whose verification condition states that
  * it cannot be reached. There is one rule, which does not depend on where the `???` is written:
  *
  *  - `???` stays an unknown value within ghost code, which is erased, and within `@extern`
  *    definitions, whose bodies are not analysed.
  *  - Otherwise, it must be unreachable whenever the body containing it may run. The body of a
  *    function that is not a method may always run. The body of a method may run when a class that
  *    can be instantiated inherits it without overriding it, or when a body that may run calls it
  *    through `super`.
  *  - The initialiser of a field runs for all the instances of the subclasses of its class, including
  *    those that override the field. It has no precondition, so a `???` within it is rejected.
  *
  * A method of an abstract class whose body is `???` is therefore the specification of an abstract
  * method, as long as all the concrete subclasses implement it:
  *
  * {{{
  * abstract class Shape {
  *   def area: BigInt = { (??? : BigInt) }.ensuring(_ >= 0) // not guarded: no class runs it
  * }
  * case class Square(side: BigInt) extends Shape {
  *   override def area: BigInt = { side * side }.ensuring(_ >= 0)
  * }
  * case class Blob() extends Shape {
  *   override def area: BigInt = { (??? : BigInt) }.ensuring(_ >= 0) // guarded: `Blob().area` runs it
  * }
  * }}}
  *
  * This runs after `Mixins` and `InnerClasses`, when the methods that classes inherit through mixin
  * composition are explicit and local classes are lifted, and before `SuperCalls`, while super calls
  * are still visible.
  */
trait UnimplementedCode extends ExtractionPipeline {
  val s: Trees
  val t: s.type
  import s._

  override def invalidate(id: Identifier): Unit = ()

  /** Why the body of a function may run. */
  private enum Reason {
    case Function
    case Inherited(cls: Identifier)
    case SuperCall(caller: Identifier)
    case Field(cls: Identifier)
  }

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    given s.Symbols = symbols

    /** The `???` of a function that are not ghost, and the methods it calls through `super` from non-ghost code. */
    class Collector(override val trees: s.type)(using override val symbols: s.Symbols) extends methods.GhostTraverser {
      val unimplemented = new IdentityHashMap[NoTree, Unit]()
      var superCalls = Set.empty[Identifier]

      private def isFalse(e: Expr): Boolean = e match {
        case BooleanLiteral(false) => true
        case Annotated(e, _) => isFalse(e)
        case _ => false
      }

      override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
        case nt: NoTree =>
          if (!ctx.isGhost) unimplemented.put(nt, ())

        // The frontend's encoding of `assert(false)`, which is unreachable already
        case Assert(pred, _, NoTree(NothingType())) if isFalse(pred) =>
          traverse(pred, ctx)

        case Let(vd, value, body) if vd.flags.exists(f => f == Ghost || f == Extern) =>
          traverse(vd, ctx)
          traverse(value, ctx.withinGhost)
          traverse(body, ctx)

        case LetVar(vd, value, body) if vd.flags.exists(f => f == Ghost || f == Extern) =>
          traverse(vd, ctx)
          traverse(value, ctx.withinGhost)
          traverse(body, ctx)

        case MethodInvocation(Super(_), id, _, _) =>
          if (!ctx.isGhost && !symbols.getFunction(id).flags.contains(Ghost)) superCalls += id
          super.traverse(e, ctx)

        case _ => super.traverse(e, ctx)
      }

      override def traverse(fd: LocalFunDef, ctx: GhostContext): Unit =
        super.traverse(fd, ctx.inGhost(fd.flags contains Extern))
    }

    val collectors: Map[Identifier, Collector] = symbols.functions.values.toSeq
      .filter(fd => !fd.flags.contains(Extern) && !fd.flags.contains(Ghost))
      .filter(fd => exprOps.exists { case _: NoTree | MethodInvocation(Super(_), _, _, _) => true case _ => false } (fd.fullBody))
      .map { fd =>
        val collector = new Collector(s)
        collector.traverse(fd)
        fd.id -> collector
      }.toMap

    if (collectors.values.forall(_.unimplemented.isEmpty)) return (symbols, ExtractionSummary.NoSummary)

    def ownerOf(fd: FunDef): Option[Identifier] = fd.flags.collectFirst { case IsMethodOf(id) => id }

    val methodsOf: Map[Identifier, Seq[FunDef]] =
      symbols.functions.values.toSeq.flatMap(fd => ownerOf(fd).map(_ -> fd)).groupMap(_._1)(_._2)

    /** The linearization of a class: the order in which Scala looks for the implementation of its methods. */
    def linearization(id: Identifier): Seq[Identifier] =
      id +: symbols.lookupClass(id).toSeq.flatMap(_.parents.map(_.id)).foldLeft(Seq.empty[Identifier]) { (acc, p) =>
        val l = linearization(p)
        l.filterNot(acc.contains) ++ acc
      }

    def symbolOf(fd: FunDef): Option[Symbol] = fd.id match {
      case sid: SymbolIdentifier => Some(sid.symbol)
      case _ => None
    }

    // The bodies that may run, starting with those of the functions that are not methods
    var reasons = Map.empty[Identifier, Reason]
    var pending = List.empty[Identifier]

    def mayRun(id: Identifier, reason: => Reason): Unit = if (!reasons.contains(id)) {
      reasons += id -> reason
      pending ::= id
    }

    for (fd <- symbols.functions.values if ownerOf(fd).isEmpty) mayRun(fd.id, Reason.Function)

    // The classes that can be instantiated run the methods that they declare or inherit, and the
    // initialisers of all the fields of their ancestors
    for (cd <- symbols.classes.values if !cd.flags.contains(IsAbstract) && !cd.flags.contains(Ghost)) {
      val lin = linearization(cd.id)
      val declared = lin.flatMap(methodsOf.getOrElse(_, Seq.empty))

      def reason(fd: FunDef): Reason =
        if (ownerOf(fd) contains cd.id) Reason.Function
        else if (fd.isField(isLazy = false)) Reason.Field(cd.id)
        else Reason.Inherited(cd.id)

      val implemented = declared
        .filterNot(_.flags contains IsAbstract)
        .distinctBy(fd => symbolOf(fd).getOrElse(fd.id))

      for (fd <- implemented ++ declared.filter(_.isField(isLazy = false))) mayRun(fd.id, reason(fd))
    }

    while (pending.nonEmpty) {
      val id = pending.head
      pending = pending.tail
      for (collector <- collectors.get(id); target <- collector.superCalls) mayRun(target, Reason.SuperCall(id))
    }

    def description(fd: FunDef): String = {
      val why = reasons(fd.id) match {
        case Reason.Function => ""
        case Reason.Inherited(cls) => s" (class ${cls.name} inherits ${fd.id.name})"
        case Reason.SuperCall(caller) =>
          val owner = symbols.getFunction(caller).flags.collectFirst { case IsMethodOf(cid) => s"${cid.name}." }.getOrElse("")
          s" ($owner${caller.name} calls ${fd.id.name} through super)"
        case Reason.Field(cls) => s" (class ${cls.name} initialises ${fd.id.name})"
      }
      UnimplementedCode.description + why
    }

    val newFunctions = symbols.functions.values.toSeq.map { fd =>
      collectors.get(fd.id) match {
        case Some(collector) if reasons.contains(fd.id) && !collector.unimplemented.isEmpty =>
          // The initialiser of a field has no precondition, and its assertions are not verified on their own
          if (fd.isField(isLazy = false)) {
            val cls = reasons(fd.id) match {
              case Reason.Field(cls) => cls
              case _ => ownerOf(fd).get
            }
            throw MethodsException(collector.unimplemented.keySet.iterator.next(),
              s"Field ${fd.id.name} is initialised with a missing implementation (???), " +
              s"which runs when an instance of class ${cls.name} is created")
          }

          val descr = description(fd)
          fd.copy(fullBody = exprOps.postMap {
            case nt: NoTree if collector.unimplemented.containsKey(nt) =>
              Some(Assert(BooleanLiteral(false).copiedFrom(nt), Some(descr), nt).copiedFrom(nt))
            case _ => None
          } (fd.fullBody)).copiedFrom(fd)

        case _ => fd
      }
    }

    val newSymbols = NoSymbols
      .withFunctions(newFunctions)
      .withSorts(symbols.sorts.values.toSeq)
      .withClasses(symbols.classes.values.toSeq)
      .withTypeDefs(symbols.typeDefs.values.toSeq)

    (newSymbols, ExtractionSummary.NoSummary)
  }
}

object UnimplementedCode {
  /** The description of the assertions that guard the `???` that may run. */
  val description: String = "Missing implementation (???) is unreachable"

  def apply(tr: Trees)(using inox.Context): ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = {
    class Impl(override val s: tr.type, override val t: tr.type)
              (using override val context: inox.Context) extends UnimplementedCode
    new Impl(tr, tr)
  }
}
