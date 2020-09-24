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
      new SoundInvariants(symbols, ctx),
      new AbstractValsOverride(symbols, ctx),
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

  /** Check that setters are only overridden by other setters */
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

  /** Check that methods are only overridden by methods with the same ghostiness */
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

    def checkBodyWithSpecs(fullBody: Expr, kindsWhitelist: Option[Set[exprOps.SpecKind]]): Unit = {
      val specced = exprOps.BodyWithSpecs(fullBody)
      kindsWhitelist.foreach { allowedKinds =>
        specced.specs.foreach(spec =>
          if (!allowedKinds.contains(spec.kind))
            errors += MalformedStainlessCode(fullBody, s"Unexpected `${spec.kind.name}` specification.")
        )
      }
      specced.specs.groupBy(_.kind).map { case (kind, specs) =>
        if (specs.length > 1)
          errors += MalformedStainlessCode(fullBody, s"Duplicate `${kind.name}` specification.")
      }
      specced.specs.foreach(s => traverse(s.expr))
      specced.bodyOpt.foreach(traverse)
    }

    override def traverse(fd: FunDef): Unit = {
      traverse(fd.id)
      fd.tparams.foreach(traverse)
      fd.params.foreach(traverse)
      traverse(fd.returnType)
      checkBodyWithSpecs(fd.fullBody, kindsWhitelist = None)
      fd.flags.foreach(traverse)
    }

    override def traverse(e: Expr): Unit = e match {
      case e: Require =>
        errors += MalformedStainlessCode(e, s"Unexpected `require`.")

      case e: Decreases =>
        errors += MalformedStainlessCode(e, s"Unexpected `decreases`.")

      case wh @ While(cond, body, optInv) =>
        traverse(cond)
        checkBodyWithSpecs(body, kindsWhitelist = Some(Set(exprOps.MeasureKind)))
        optInv.foreach(traverse)

      case e: LetRec =>
        // Traverse LocalFunDef independently
        e.fds.foreach { case LocalFunDef(id, tparams, params, returnType, fullBody, flags) =>
          traverse(id)
          tparams.foreach(traverse)
          params.foreach(traverse)
          traverse(returnType)
          checkBodyWithSpecs(fullBody, kindsWhitelist = None)
          flags.foreach(traverse)
        }

        traverse(e.body)

      case e: Lambda =>
        e.params.foreach(traverse)
        checkBodyWithSpecs(e.body, kindsWhitelist = Some(Set(exprOps.PreconditionKind)))

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
      symbols.getFunction(id).isAccessor

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

  /** Check that invariants only refer to the fields of their enclosing class, and not methods */
  private[this] class SoundInvariants(syms: Symbols, ctx: inox.Context) extends Sanitizer(syms, ctx) {

    var errors: ListBuffer[MalformedStainlessCode] = ListBuffer.empty

    override def sanitize(): Seq[MalformedStainlessCode] = {
      errors = ListBuffer.empty
      symbols.functions.values.filter(_.isInvariant).foreach(check)
      errors.toSeq
    }

    private[this] def check(inv: FunDef): Unit = {
      if (inv.hasPrecondition) {
        errors += MalformedStainlessCode(inv, "Invariants cannot have preconditions")
      }

      if (inv.hasPostcondition) {
        errors += MalformedStainlessCode(inv, "Invariants cannot have postconditions")
      }

      if (!inv.isMethod) {
        errors += MalformedStainlessCode(inv, "Only methods of a class can be annotated with @invariant")
      }

      checkThisUsage(inv.fullBody)
    }

    private[this] def isAccessor(id: Identifier): Boolean = {
      symbols.getFunction(id).isAccessor
    }

    private[this] def checkThisUsage(c: MatchCase): Unit = {
      c.optGuard.foreach(checkThisUsage)
      checkThisUsage(c.rhs)
    }

    private[this] def checkThisUsage(e: Expr): Unit = {
      e match {
        case ClassSelector(This(_), _)              => ()
        case LocalClassSelector(LocalThis(_), _, _) => ()

        case MethodInvocation(This(_), id, _, args) if isAccessor(id) =>
          args.foreach(checkThisUsage)

        case LocalMethodInvocation(LocalThis(_), vd, _, _, args) if isAccessor(vd.id) =>
          args.foreach(checkThisUsage)

        case MatchExpr(_: This | _: LocalThis, cases) =>
          cases.foreach {
            case c if c.pattern.binder.isDefined =>
              errors += MalformedStainlessCode(c, "Binding `this` in a match case within an invariant is unsound")
            case c if c.pattern.isInstanceOf[UnapplyPattern] =>
              errors += MalformedStainlessCode(c, "Matching `this` against an unapply pattern within an invariant is unsound")
            case _ => ()
          }

          cases.foreach(checkThisUsage)

        case t: This =>
          errors += MalformedStainlessCode(t, "Calling a method or function on `this` within an invariant is unsound")
        case l: LocalThis =>
          errors += MalformedStainlessCode(l, "Calling a method or function on `this` within an invariant is unsound")

        case e =>
          val Operator(es, _) = e
          es.foreach(checkThisUsage)
      }
    }
  }

  /** Check that abstract vals are only overridden by constructor parameters */
  private[this] class AbstractValsOverride(syms: Symbols, ctx: inox.Context) extends Sanitizer(syms, ctx) {

    var errors: ListBuffer[MalformedStainlessCode] = ListBuffer.empty

    override def sanitize(): Seq[MalformedStainlessCode] = {
      errors = ListBuffer.empty
      symbols.classes.values.filter(_.isAbstract).foreach(check)
      errors.toSeq
    }

    private[this] def symbolOf(defn: Definition): Symbol =
      defn.id.asInstanceOf[SymbolIdentifier].symbol


    private[this] def check(cd: ClassDef): Unit = {

      // `val` in abstract classes can only be overridden by a constructor parameter
      val abstractFields = cd.methods
        .map(symbols.getFunction)
        .filter(fd => fd.isAbstract && fd.isGetter)
        .map(fd => symbolOf(fd) -> fd)
        .toMap

      val abstractFieldSymbols = abstractFields.keys.toSet

      cd.descendants.foreach {
        case desc if desc.isAbstract =>
          val methods = desc.methods
            .map(symbols.getFunction)
            .map(fd => symbolOf(fd) -> fd)
            .toMap

          val methodSymbols = methods.keys.toSet

          val wrongOverrides = methodSymbols & abstractFieldSymbols
          wrongOverrides foreach { sym =>
            errors += MalformedStainlessCode(methods(sym),
              s"Abstract values can only be overridden in concrete subclasses (with a field)")
          }

        case desc =>
          val methods = desc.methods.map(symbols.getFunction)
          val fieldSymbols = desc.fields.map(symbolOf).toSet
          val accessorSymbols = desc.fields.map { vd =>
            val accessor = methods.find { fd => fd.isGetter && fd.isAccessor(vd.id) }
            symbolOf(accessor.get) // Safe: All fields have accessors
          }

          val allSymbols = fieldSymbols ++ accessorSymbols

          if (!abstractFieldSymbols.subsetOf(allSymbols)) {
            val missing = abstractFieldSymbols -- allSymbols
            val vals = missing.map(abstractFields(_)).map(_.id.asString).mkString("`", "`, `", "`")
            errors += MalformedStainlessCode(desc, s"Abstract values $vals must be overridden with fields in concrete subclass")
          }
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
