/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package xlang

/** Inspect trees, detecting illegal structures. */
trait TreeSanitizer {

  val trees: xlang.Trees
  import trees._

  /** Throw a [[MissformedStainlessCode]] exception when detecting an illegal pattern. */
  def check(symbols: Symbols): Unit = {
    val preconditions = new CheckPreconditions()(symbols)
    symbols.functions.values foreach preconditions.traverse

    val ignored = new CheckIgnoredFields()(symbols)
    symbols.functions.values foreach ignored.traverse
  }

  /* This detects both multiple `require` and `require` after `decreases`. */
  private class CheckPreconditions(implicit symbols: Symbols) extends TreeTraverser {
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
        throw MissformedStainlessCode(e, s"Unexpected `require`.")

      case e: Decreases =>
        throw MissformedStainlessCode(e, s"Unexpected `decreases`.")

      case e: LetRec =>
        // Traverse LocalFunDef independently
        e.fds.foreach { case LocalFunDef(name, tparams, lambda) =>
          traverse(name)
          tparams.foreach(traverse)
          lambda.params.foreach(traverse)
          val (specs, body) = exprOps.deconstructSpecs(lambda.body)
          specs.foreach(s => traverse(s.expr))
          body.foreach(traverse)
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

  /* This detects accesses to @ignored fields */
  private class CheckIgnoredFields(implicit symbols: Symbols) extends TreeTraverser {
    override def traverse(e: Expr): Unit = e match {
      case e @ ClassSelector(obj, selector) =>
        val ct = obj.getType.asInstanceOf[ClassType]
        ct.getField(selector) match {
          case None =>
            throw MissformedStainlessCode(e, s"Cannot find field `$selector` of class $ct.")
          case Some(field) if field.flags contains Ignore =>
            throw MissformedStainlessCode(e, s"Cannot access ignored field `$selector` from non-extern context.")
          case _ =>
            super.traverse(e)
        }

      case e @ ClassConstructor(ct, args) =>
        ct.lookupClass match {
          case None =>
            throw MissformedStainlessCode(e, s"Cannot find class for type `$ct`.")

          case Some(tcd) if tcd.fields.exists(_.flags contains Ignore) =>
            val ignoredFields = tcd.fields.filter(_.flags contains Ignore).map(_.id).mkString(", ")
            throw MissformedStainlessCode(
              e,
              s"Cannot build an instance of a class with ignored fields in non-extern context " +
              s"($ct has ignored fields: $ignoredFields)."
            )

          case _ => super.traverse(e)
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
