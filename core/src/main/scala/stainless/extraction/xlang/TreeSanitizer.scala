/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package xlang

import scala.collection.mutable.ListBuffer

/** Inspect trees, detecting illegal structures. */
trait TreeSanitizer {

  val trees: xlang.Trees
  import trees._

  /** Throw a [[MalformedStainlessCode]] exception when detecting an illegal pattern. */
  def check(symbols: Symbols)(implicit ctx: inox.Context): Seq[MalformedStainlessCode] = {
    val checks = List(
      new Preconditions(symbols, ctx),
      new IgnoredFields(symbols, ctx),
      new SettersOverrides(symbols, ctx),
      new SealedClassesChildren(symbols, ctx),
      new SoundEquality(symbols, ctx),
    )

    checks.flatMap(_.sanitize)
  }

  def enforce(symbols: Symbols)(implicit ctx: inox.Context): Unit = {
    import ctx.reporter

    val errors = check(symbols)
    if (!errors.isEmpty) {
      errors foreach { error =>
        reporter.error(error.tree.getPos, error.getMessage)
      }
    }
  }

  private[this] abstract class Sanitizer(syms: Symbols, ctx: inox.Context) {
    protected implicit val symbols: Symbols = syms
    protected implicit val context: inox.Context = ctx
    protected implicit val printerOpts: PrinterOptions = PrinterOptions.fromSymbols(symbols, ctx)

    def sanitize(): Seq[MalformedStainlessCode]
  }

  /** check that setters are only overriden by other setters */
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

  /** Disallow equality between lambdas and non-sealed abstract classes in non-ghost code */
  private[this] class SoundEquality(syms: Symbols, ctx: inox.Context)
    extends Sanitizer(syms, ctx) with SelfTreeTraverser {

    final val PEDANTIC = true

    private[this] var errors: ListBuffer[MalformedStainlessCode] = ListBuffer.empty

    private[this] var ghostContext: Boolean = false

    private[this] def withinGhostContext[A](body: => A): A = {
      val old = ghostContext
      ghostContext = true
      val res = body
      ghostContext = old
      res
    }


    override def sanitize(): Seq[MalformedStainlessCode] = {
      errors = ListBuffer.empty
      ghostContext = false
      symbols.functions.values.toSeq.foreach(traverse)
      errors.toSeq
    }

    override def traverse(fd: FunDef): Unit = {
      if (fd.flags contains Ghost)
        withinGhostContext(super.traverse(fd))
      else
        super.traverse(fd)
    }

    private[this] val hasLocalSubClasses: Identifier => Boolean =
      symbols.localClasses.flatMap(_.globalAncestors.map(_.id)).toSet

    private[this] def isOrHasNonSealedAncestors(ct: ClassType): Boolean = {
      val ancestors = (ct.tcd +: ct.tcd.ancestors)
      ancestors.exists(tcd => tcd.cd.isAbstract && !tcd.cd.isSealed)
    }

    override def traverse(e: Expr): Unit = e match {
      case Annotated(body, flags) if flags contains Ghost =>
        withinGhostContext(traverse(body))

      case Decreases(_, body) =>
        withinGhostContext(traverse(body))

      case Snapshot(body) =>
        withinGhostContext(traverse(body))

      case FunctionInvocation(id, _, args) if symbols.getFunction(id).flags contains Ghost =>
        withinGhostContext {
          args foreach traverse
        }

      case FunctionInvocation(id, _, args) =>
        val fd = symbols.getFunction(id)
        (fd.params zip args) foreach {
          case (vd, arg) if vd.flags contains Ghost =>
            withinGhostContext(traverse(arg))
          case (_, arg) =>
            traverse(arg)
        }

      case MethodInvocation(rec, id, _, args) if symbols.getFunction(id).flags contains Ghost =>
        traverse(rec)
        withinGhostContext {
          args foreach traverse
        }

      case MethodInvocation(rec, id, _, args) =>
        traverse(rec)
        val fd = symbols.getFunction(id)
        (fd.params zip args) foreach {
          case (vd, arg) if vd.flags contains Ghost =>
            withinGhostContext(traverse(arg))
          case (_, arg) =>
            traverse(arg)
        }

      case ADT(id, _, args) =>
        (symbols.getConstructor(id).fields zip args) foreach {
          case (vd, arg) if vd.flags contains Ghost =>
            withinGhostContext(traverse(arg))
          case (_, arg) =>
            traverse(arg)
        }

      case ClassConstructor(ct, args) =>
        (ct.tcd.fields zip args).foreach {
          case (vd, arg) if vd.flags contains Ghost =>
            withinGhostContext(traverse(arg))
          case (_, arg) =>
            traverse(arg)
        }

      case Equals(lhs, rhs) if !ghostContext =>
        (lhs.getType, rhs.getType) match {
          case (ct1: ClassType, ct2) if hasLocalSubClasses(ct1.id) =>
            errors += MalformedStainlessCode(e, "Cannot compare classes with local subclasses for equality")
          case (ct1, ct2: ClassType) if hasLocalSubClasses(ct2.id) =>
            errors += MalformedStainlessCode(e, "Cannot compare classes with local subclasses for equality")

          case (ct1: ClassType, ct2) if PEDANTIC && isOrHasNonSealedAncestors(ct1) =>
            errors += MalformedStainlessCode(e, "Cannot compare classes with non sealed ancestors for equality in non-ghost code")
          case (ct1, ct2: ClassType) if PEDANTIC && isOrHasNonSealedAncestors(ct2) =>
            errors += MalformedStainlessCode(e, "Cannot compare classes with non sealed ancestors for equality in non-ghost code")

          case (lct1: LocalClassType, lct2) =>
            errors += MalformedStainlessCode(e, "Cannot compare local classes for equality in non-ghost code")
          case (lct1, lct2: LocalClassType) =>
            errors += MalformedStainlessCode(e, "Cannot compare local classes for equality in non-ghost code")

          case (ft1: FunctionType, ft2) =>
            errors += MalformedStainlessCode(e, "Cannot compare lambdas for equality in non-ghost code")
          case (ft1, ft2: FunctionType) =>
            errors += MalformedStainlessCode(e, "Cannot compare lambdas for equality in non-ghost code")

          case _ => ()
        }

      case _ => super.traverse(e)
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
