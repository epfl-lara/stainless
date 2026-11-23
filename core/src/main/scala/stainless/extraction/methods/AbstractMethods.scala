/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package extraction
package methods

/** Checks the use of `AbstractMethodBody()`, the body of the abstract methods that have a specification.
  *
  * A missing implementation `???` is an `assert(false)` wherever it is written: Scala throws an
  * exception when it evaluates it, so it must be unreachable. The frontend extracts it that way.
  * The specification of an abstract method is written with `AbstractMethodBody()` instead:
  *
  * {{{
  * abstract class Shape {
  *   def area: BigInt = { AbstractMethodBody[BigInt]() }.ensuring(_ >= 0)
  * }
  * case class Square(side: BigInt) extends Shape {
  *   override def area: BigInt = { side * side }.ensuring(_ >= 0)
  * }
  * }}}
  *
  * Such a body never runs, which this phase ensures without verification conditions:
  *
  *  - `AbstractMethodBody()` is the whole body of a method of an abstract class or of a trait, apart
  *    from its specification, and the method is neither final nor private. It is then abstract,
  *    and the well-formedness of the classes (see `Trees.ensureWellFormedClass`) requires the
  *    concrete classes to implement it.
  *  - An abstract method is not called through `super`.
  *  - The initialiser of a field is not a missing implementation, as it runs for all the instances.
  *
  * This runs after `Mixins` and `InnerClasses`, when local classes are lifted, and before
  * `SuperCalls`, while super calls are still visible.
  */
trait AbstractMethods extends ExtractionPipeline {
  val s: Trees
  val t: s.type
  import s._

  override def invalidate(id: Identifier): Unit = ()

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    given s.Symbols = symbols

    def isMissingImplementation(e: Expr): Boolean = e match {
      case Assert(_, Some(AbstractMethods.missingImplementation), _) => true
      case _ => false
    }

    /** The `AbstractMethodBody()` of an expression: the `NoTree` that do not come after an `assert(false)`. */
    def abstractBodies(e: Expr): Seq[NoTree] = {
      var res = Seq.empty[NoTree]
      def isFalse(e: Expr): Boolean = e match {
        case BooleanLiteral(false) => true
        case Annotated(e, _) => isFalse(e)
        case _ => false
      }
      def rec(e: Expr): Unit = e match {
        case nt: NoTree => res :+= nt
        case Assert(pred, _, NoTree(_)) if isFalse(pred) => ()
        // The values of `@extern` variables and the bodies of `@extern` local functions are not analysed
        case Let(vd, _, body) if vd.flags contains Extern => rec(body)
        case LetVar(vd, _, body) if vd.flags contains Extern => rec(body)
        case LetRec(fds, body) =>
          fds.filterNot(_.flags contains Extern).foreach(fd => rec(fd.fullBody))
          rec(body)
        case Operator(es, _) => es.foreach(rec)
      }
      rec(e)
      res
    }

    for (fd <- symbols.functions.values) {
      val cdOpt = fd.flags.collectFirst { case IsMethodOf(id) => symbols.getClass(id) }

      if (!fd.flags.contains(Extern) && !fd.flags.contains(IsAbstract) && !fd.flags.contains(Synthetic)) {
        val bodies = abstractBodies(fd.fullBody)
        val isWholeBody = bodies.size == 1 && !fd.hasBody
        val isField = fd.flags.exists { case IsField(_) => true case _ => false }
        if (bodies.nonEmpty && !(isWholeBody && !isField && cdOpt.exists(_.isAbstract))) {
          throw MethodsException(bodies.head,
            "AbstractMethodBody() can only be the body of a method of an abstract class or of a trait")
        }
        if (bodies.nonEmpty && fd.flags.exists(f => f == Final || f == Private)) {
          throw MethodsException(bodies.head,
            s"AbstractMethodBody() cannot be the body of ${fd.id.name}: a final or private method cannot be overridden")
        }
      }

      // The initialiser of a field has no precondition, and it runs for all the instances of the class
      if (fd.isField(isLazy = false)) {
        exprOps.collect[Expr] { case e if isMissingImplementation(e) => Set(e) case _ => Set() } (fd.fullBody).headOption foreach { e =>
          throw MethodsException(e,
            s"Field ${fd.id.name} is initialised with a missing implementation (???), " +
            s"which runs when an instance of class ${cdOpt.map(_.id.name).getOrElse("its class")} is created")
        }
      }

      exprOps.preTraversal {
        case e @ MethodInvocation(Super(_), id, _, _) if symbols.getFunction(id).isAbstract =>
          throw MethodsException(e, s"Abstract method ${id.name} cannot be called through super")
        case _ => ()
      } (fd.fullBody)
    }

    (symbols, ExtractionSummary.NoSummary)
  }
}

object AbstractMethods {
  /** The description of the assertions that the frontend extracts for `???`. */
  val missingImplementation: String = "Missing implementation (???) is unreachable"

  def apply(tr: Trees)(using inox.Context): ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = {
    class Impl(override val s: tr.type, override val t: tr.type)
              (using override val context: inox.Context) extends AbstractMethods
    new Impl(tr, tr)
  }
}
