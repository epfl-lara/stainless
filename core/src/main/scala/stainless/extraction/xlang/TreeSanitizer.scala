/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package xlang

import scala.collection.mutable.ListBuffer

/** Inspect trees, detecting illegal structures. */
trait TreeSanitizer { self =>

  val trees: xlang.Trees
  import trees._

  object TypeOperator extends {
    protected val s: self.trees.type = self.trees
    protected val t: self.trees.type = self.trees
  } with inox.ast.TreeExtractor {
    type Source = Type
    type Target = Type

    def unapply(t: Type): Option[(Seq[Type], Seq[Type] => Type)] = {
      val (ids, vs, es, tps, flags, builder) = deconstructor.deconstruct(t)
      Some((tps, tpss => builder(ids, vs, es, tpss, flags)))
    }
  }


  /** Throw a [[MalformedStainlessCode]] exception when detecting an illegal pattern. */
  def check(symbols: Symbols)(implicit ctx: inox.Context): Seq[MalformedStainlessCode] = {
    val checks = List(
      new Preconditions(symbols, ctx),
      new IgnoredFields(symbols, ctx),
      new SettersOverrides(symbols, ctx),
      new GhostOverrides(symbols, ctx),
      new SealedClassesChildren(symbols, ctx),
      new SoundEquality(symbols, ctx),
    )

    checks.flatMap(_.sanitize.distinct).sortBy(_.tree.getPos)
  }

  def enforce(symbols: Symbols)(implicit ctx: inox.Context): Seq[MalformedStainlessCode] = {
    import ctx.reporter

    val errors = check(symbols)
    if (!errors.isEmpty) {
      errors foreach { error =>
        reporter.error(error.tree.getPos, error.getMessage)
      }
    }
    errors
  }

  private[this] abstract class Sanitizer(syms: Symbols, ctx: inox.Context) {
    protected implicit val symbols: Symbols = syms
    protected implicit val context: inox.Context = ctx
    protected implicit val printerOpts: PrinterOptions = PrinterOptions.fromSymbols(symbols, ctx)

    def sanitize(): Seq[MalformedStainlessCode]
  }

  /** Check that setters are only overriden by other setters */
  private[this] class SettersOverrides(syms: Symbols, ctx: inox.Context) extends Sanitizer(syms, ctx) {
    override def sanitize(): Seq[MalformedStainlessCode] = {
      for {
        cd <- symbols.classes.values.toSeq
        id <- cd.methods(symbols)
        if !symbols.getFunction(id).isSetter
        sid <- symbols.firstSuperMethod(id)
        if symbols.getFunction(sid).isSetter
      } yield MalformedStainlessCode(symbols.getFunction(id),
        "Cannot override a `var` accessor with a non-accessor method.")
    }
  }

  /** Check that methods are only overriden by methods with the same ghostiness */
  private[this] class GhostOverrides(syms: Symbols, ctx: inox.Context) extends Sanitizer(syms, ctx) {
    override def sanitize(): Seq[MalformedStainlessCode] = {
      for {
        cd  <- symbols.classes.values.toSeq
        id  <- cd.methods(symbols)
        sid <- symbols.firstSuperMethod(id)
        isGhostOverride = symbols.getFunction(id).isGhost
        isGhostSuper = symbols.getFunction(sid).isGhost
        if isGhostOverride != isGhostSuper
      } yield MalformedStainlessCode(
        symbols.getFunction(id),
        if (isGhostSuper) s"Cannot override ghost method ${sid.asString} with non-ghost method"
        else s"Cannot override non-ghost method ${sid.asString} with ghost method"
      )
    }
  }

  /** Check that sealed traits have children */
  private[this] class SealedClassesChildren(syms: Symbols, ctx: inox.Context) extends Sanitizer(syms, ctx) {
    private[this] val hasLocalSubClasses: Identifier => Boolean =
      symbols.localClasses.flatMap(_.globalAncestors.map(_.id)).toSet

    def sanitize(): Seq[MalformedStainlessCode] = {
      for {
        cd <- symbols.classes.values.toSeq
        if cd.isAbstract && cd.isSealed && !hasLocalSubClasses(cd.id) && cd.children(symbols).isEmpty
      } yield MalformedStainlessCode(cd, "Illegal sealed abstract class with no children.")
    }
  }

  /* This detects both multiple `require` and `require` after `decreases`. */
  private[this] class Preconditions(syms: Symbols, ctx: inox.Context)
    extends Sanitizer(syms, ctx) with SelfTreeTraverser {

    private[this] var errors: ListBuffer[MalformedStainlessCode] = ListBuffer.empty

    def sanitize(): Seq[MalformedStainlessCode] = {
      errors = ListBuffer.empty
      symbols.functions.values.toSeq.foreach(traverse)
      errors.toSeq
    }

    override def traverse(fd: FunDef): Unit = {
      traverse(fd.id)
      fd.tparams.foreach(traverse)
      fd.params.foreach(traverse)
      traverse(fd.returnType)
      val (specs, body) = exprOps.deconstructSpecs(fd.fullBody)
      specs.foreach(s => traverse(s.expr))
      body.foreach(traverse)
      fd.flags.foreach(traverse)
    }

    override def traverse(e: Expr): Unit = e match {
      case wh @ While(cond, body, optInv) =>
        traverse(cond)
        val (specs, without) = exprOps.deconstructSpecs(body)
        val (measures, otherSpecs) = specs.partition { case exprOps.Measure(_) => true case _ => false }
        measures.foreach(s => traverse(s.expr))
        traverse(exprOps.reconstructSpecs(otherSpecs, without, body.getType))
        optInv.foreach(traverse)

      case e: Require =>
        errors += MalformedStainlessCode(e, s"Unexpected `require`.")

      case e: Decreases =>
        errors += MalformedStainlessCode(e, s"Unexpected `decreases`.")

      case e: LetRec =>
        // Traverse LocalFunDef independently
        e.fds.foreach { case LocalFunDef(id, tparams, params, returnType, fullBody, flags) =>
          traverse(id)
          tparams.foreach(traverse)
          params.foreach(traverse)
          traverse(returnType)
          val (specs, body) = exprOps.deconstructSpecs(fullBody)
          specs.foreach(s => traverse(s.expr))
          body.foreach(traverse)
          flags.foreach(traverse)
        }

        traverse(e.body)

      case e: Lambda =>
        e.params.foreach(traverse)
        val (specs, body) = exprOps.deconstructSpecs(e.body)
        val (preconditions, otherSpecs) = specs.partition { case exprOps.Precondition(_) => true case _ => false }
        preconditions.foreach(s => traverse(s.expr))
        traverse(exprOps.reconstructSpecs(otherSpecs, body, e.body.getType))

      case _ => super.traverse(e)
    }
  }

  /** Detects accesses to @ignored fields */
  private[this] class IgnoredFields(syms: Symbols, ctx: inox.Context)
    extends Sanitizer(syms, ctx) with SelfTreeTraverser {

    private[this] var errors: ListBuffer[MalformedStainlessCode] = ListBuffer.empty

    override def sanitize(): Seq[MalformedStainlessCode] = {
      errors = ListBuffer.empty
      symbols.functions.values.toSeq.foreach(traverse)
      errors.toSeq
    }

    private def isFieldAccessor(id: Identifier): Boolean =
      symbols.getFunction(id).flags exists { case IsAccessor(_) => true case _ => false }

    override def traverse(e: Expr): Unit = e match {
      case ClassSelector(obj, selector) =>
        val ct = obj.getType.asInstanceOf[ClassType]
        ct.getField(selector) match {
          case None =>
            errors += MalformedStainlessCode(e, s"Cannot find field `${selector.asString}` of class ${ct.asString}.")
          case Some(field) if field.flags contains Ignore =>
            errors += MalformedStainlessCode(e, s"Cannot access ignored field `${selector.asString}` from non-extern context.")
          case _ =>
            super.traverse(e)
        }

      case MethodInvocation(rec, id, tps, args) if isFieldAccessor(id) =>
        symbols.getFunction(id).flags collectFirst { case IsAccessor(Some(id)) => id } match {
          case Some(id) if rec.getType.isInstanceOf[ClassType] =>
            val ct = rec.getType.asInstanceOf[ClassType]
            ct.getField(id) match {
              case Some(field) if field.flags contains Ignore =>
                errors += MalformedStainlessCode(e, s"Cannot access ignored field `${id.asString}` from non-extern context.")
              case None if symbols.lookupFunction(id).exists(_.flags contains Ignore) =>
                errors += MalformedStainlessCode(e, s"Cannot access ignored field `${id.asString}` from non-extern context.")
              case _ =>
                super.traverse(e)
            }
          case _ =>
            super.traverse(e)
        }

      case ClassConstructor(ct, args) =>
        ct.lookupClass match {
          case None =>
            errors += MalformedStainlessCode(e, s"Cannot find class for type `${ct.asString}`.")

          case Some(tcd) if tcd.fields.exists(_.flags contains Ignore) =>
            val ignoredFields = tcd.fields.filter(_.flags contains Ignore).map(_.id.asString).mkString(", ")
            errors += MalformedStainlessCode(e,
              s"Cannot build an instance of a class with ignored fields in non-extern context " +
              s"(${ct.asString} has ignored fields: $ignoredFields)."
            )

          case _ => super.traverse(e)
        }

      case _ => super.traverse(e)
    }
  }

  /** Disallow equality tests between lambdas and non-sealed abstract classes in non-ghost code */
  private[this] class SoundEquality(syms: Symbols, ctx: inox.Context) extends Sanitizer(syms, ctx) { sanitizer =>

    val PEDANTIC = false

    var errors: ListBuffer[MalformedStainlessCode] = ListBuffer.empty

    override def sanitize(): Seq[MalformedStainlessCode] = {
      errors = ListBuffer.empty
      symbols.functions.values.toSeq.foreach(ghostTraverser.traverse)
      errors.toSeq
    }

    val hasLocalSubClasses: Identifier => Boolean =
      symbols.localClasses.flatMap(_.globalAncestors.map(_.id)).toSet

   def isOrHasNonSealedAncestors(ct: ClassType): Boolean = {
      val ancestors = (ct.tcd +: ct.tcd.ancestors)
      ancestors.exists(tcd => tcd.cd.isAbstract && !tcd.cd.isSealed)
    }

    object ghostTraverser extends xlang.GhostTraverser {
      override val trees: self.trees.type = self.trees
      import trees._

      override implicit val symbols = sanitizer.symbols

      override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
        case Equals(lhs, rhs) if !ctx.isGhost =>
          def rec(tp: Type): Unit = tp match {
            case tp if PEDANTIC && typeOps.isParametricType(tp) =>
              errors += MalformedStainlessCode(e,
                s"Testing parametric types for equality, use the === method of the Eq typeclass instead")

            case ct: ClassType if hasLocalSubClasses(ct.id) =>
              errors += MalformedStainlessCode(e,
                "Testing classes with local subclasses for equality in non-ghost code is unsound")

            case ct: ClassType if isOrHasNonSealedAncestors(ct) =>
              errors += MalformedStainlessCode(e,
                "Testing classes with non sealed ancestors for equality in non-ghost code is unsound")

            case lct: LocalClassType =>
              errors += MalformedStainlessCode(e,
                "Testing local classes for equality in non-ghost code is unsound")

            case ft: FunctionType =>
              errors += MalformedStainlessCode(e, "Testing lambdas for equality in non-ghost code is unsound")

            case tp =>
              val TypeOperator(es, _) = tp
              es.foreach(rec)
          }

          rec(lhs.getType)
          rec(rhs.getType)

        case _ => super.traverse(e, ctx)
      }
    }
  }
}

object TreeSanitizer {
  def apply(tr: xlang.Trees)(implicit ctx: inox.Context): TreeSanitizer { val trees: tr.type } = {
    new TreeSanitizer {
      override val trees: tr.type = tr
    }
  }
}
