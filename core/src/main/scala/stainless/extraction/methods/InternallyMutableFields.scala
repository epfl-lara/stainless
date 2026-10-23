/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package extraction
package methods

/** Checks the accesses to `@internallyMutable` fields (this phase does not transform anything).
  *
  * An `@internallyMutable` field of a class `C` may only be read or written on `this`, from a method
  * of `C` that is either observationally pure, ghost, the class invariant, or a synthetic/accessor
  * member (such as the getter and setter of the field, or `copy$default$n`). This includes the
  * specifications and local functions of such a method. `@pure` and private methods are not allowed,
  * since a public method could then expose the field to callers.
  *
  * Calls to the accessors of the field, or to synthetic methods that read it (e.g. `copy$default$n`,
  * called by `copy`), count as accesses to the field. Binding the field in a pattern is not allowed.
  *
  * This runs before `MethodLifting`, while methods are still attached to their class and `this` is explicit.
  */
trait InternallyMutableFields extends ExtractionPipeline {
  val s: Trees
  val t: s.type
  import s._

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    // Internally mutable field identifier -> identifier of the class declaring it
    val imFields: Map[Identifier, Identifier] = symbols.classes.values.flatMap { cd =>
      cd.fields.collect { case vd if vd.flags.contains(IsInternallyMutable) => vd.id -> cd.id }
    }.toMap

    if (imFields.nonEmpty) {
      given s.Symbols = symbols
      symbols.functions.values.foreach(checkFunction(_, imFields))
    }
    (symbols, ExtractionSummary.NoSummary)
  }

  override def invalidate(id: Identifier): Unit = ()

  private def isAllowedMethod(fd: FunDef): Boolean = fd.flags.exists {
    case IsObservationallyPure | IsInvariant | Ghost | Synthetic | IsAccessor(_) => true
    case _ => false
  }

  private def isThis(e: Expr): Boolean = e match {
    case _: This => true
    case Old(e) => isThis(e)
    case Snapshot(e) => isThis(e)
    case Annotated(e, _) => isThis(e)
    case _ => false
  }

  /** The internally mutable fields that a call to `callee` accesses on its receiver. */
  private def accessedThroughCall(callee: FunDef, imFields: Map[Identifier, Identifier]): Set[Identifier] = {
    val viaAccessor = callee.flags.collect { case IsAccessor(Some(fid)) if imFields.contains(fid) => fid }.toSet
    val viaSynthetic =
      if (!callee.flags.contains(Synthetic)) Set.empty[Identifier]
      else exprOps.collect[Identifier] {
        case ClassSelector(recv, fid) if imFields.contains(fid) && isThis(recv) => Set(fid)
        case FieldAssignment(recv, fid, _) if imFields.contains(fid) && isThis(recv) => Set(fid)
        case _ => Set.empty
      }(callee.fullBody)
    viaAccessor ++ viaSynthetic
  }

  private def checkFunction(fd: FunDef, imFields: Map[Identifier, Identifier])(using symbols: s.Symbols): Unit = {
    // The class whose internally mutable fields may be accessed (on `this`) from `fd`, if any
    val allowedClass: Option[Identifier] =
      if (isAllowedMethod(fd)) fd.flags.collectFirst { case IsMethodOf(cid) => cid } else None

    def checkAccess(fid: Identifier, recv: Expr, pos: Expr): Unit = {
      val cid = imFields(fid)
      if (!(allowedClass.contains(cid) && isThis(recv)))
        throw MethodsException(pos,
          s"Field ${fid.asString} of class ${cid.asString} is @internallyMutable: it can only be accessed on `this`, " +
          s"from observationally pure, ghost, or invariant methods of ${cid.asString}")
    }

    object Checker extends ConcreteOOSelfTreeTraverser {
      override def traverse(e: Expr): Unit = {
        e match {
          case ClassSelector(recv, fid) if imFields.contains(fid) => checkAccess(fid, recv, e)
          case FieldAssignment(recv, fid, _) if imFields.contains(fid) => checkAccess(fid, recv, e)
          case MethodInvocation(recv, id, _, _) =>
            symbols.lookupFunction(id).foreach { callee =>
              accessedThroughCall(callee, imFields).foreach(fid => checkAccess(fid, recv, e))
            }
          case _ => ()
        }
        super.traverse(e)
      }

      override def traverse(pat: Pattern): Unit = {
        pat match {
          case ClassPattern(_, ct, subPatterns) =>
            symbols.lookupClass(ct.id).foreach { cd =>
              cd.fields.zip(subPatterns).foreach {
                case (field, sub) if imFields.contains(field.id) && sub != WildcardPattern(None) =>
                  throw MethodsException(sub,
                    s"Field ${field.id.asString} of class ${cd.id.asString} is @internallyMutable and cannot be bound in a pattern")
                case _ => ()
              }
            }
          case _ => ()
        }
        super.traverse(pat)
      }
    }
    Checker.traverse(fd.fullBody)
  }
}

object InternallyMutableFields {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type)(using override val context: inox.Context)
      extends InternallyMutableFields
    new Impl(trees, trees)
  }
}
