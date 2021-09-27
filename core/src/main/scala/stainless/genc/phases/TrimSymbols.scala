/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import extraction.throwing.{trees => tt}

import ExtraOps._

import collection.mutable.{Set => MutableSet}

/*
 * Compute the subset of symbols on which `@cCode.export` functions depend
 * Generic functions cannot be marked `@cCode.export` (only specialized versions that are
 * used by exported functions are exported to C).
 *
 * NOTE We cannot rely on purescala.DependencyFinder as it will traverse functions
 *     annotated with @cCode.function and we don't want that. The same applies for
 *     classes annotated with @cCode.typdef. We therefore implement a simpler version
 *     of it here based on a TreeTraverser.
 */
trait TrimSymbols extends LeonPipeline[tt.Symbols, tt.Symbols] {
  val name = "Symbol trimmer"

  implicit val context: inox.Context
  import context._

  def run(syms: tt.Symbols): tt.Symbols = {
    implicit val symbols = syms
    implicit val printerOpts = tt.PrinterOptions.fromContext(context)

    def validateClassAnnotations(cd: tt.ClassDef): Unit = {

      val pos = cd.getPos

      if (cd.isManuallyTyped && cd.isDropped)
        reporter.fatalError(pos, s"${cd.id} cannot be both dropped and manually defined")

      if (cd.isGeneric && cd.isManuallyTyped)
        reporter.fatalError(
          pos,
          s"${cd.id} cannot be both a generic type and manually defined"
        )

      if (cd.isGeneric && cd.isExported)
        reporter.fatalError(
          pos,
          s"Generic classes (${cd.id.asString}) cannot be exported"
        )

      if (cd.isManuallyTyped && cd.parents.nonEmpty)
        reporter.fatalError(
          pos,
          s"${cd.id} cannot be manually defined because it is part of a class hierarchy"
        )

      if (cd.isRecursive)
        reporter.fatalError(pos, s"${cd.id} and other recursive types are not supported")
      if (!cd.isManuallyTyped) {
        if (cd.isRecursive)
          reporter.fatalError("Recursive types are not supported")
      }
    }

    def validateFunAnnotations(fd: tt.FunDef): Unit = {
      val pos = fd.getPos

      if (fd.isManuallyDefined && fd.isDropped)
        reporter.fatalError(
          pos,
          s"Functions (${fd.id.asString}) cannot be dropped and manually implemented at the same time"
        )

      if (fd.isGeneric && fd.isManuallyDefined)
        reporter.fatalError(
          pos,
          s"Functions (${fd.id.asString}) cannot be both a generic function and manually defined"
        )

      if (fd.isGeneric && fd.isExported)
        reporter.fatalError(
          pos,
          s"Generic functions (${fd.id.asString}) cannot be exported"
        )
    }

    val trim = new Trimmer {
      override val symbols = syms
      override val s: tt.type = tt
      override val t: tt.type = tt
      val ctx = context
    }
    val newSymbols = trim.transform(syms)

    for (fd <- newSymbols.functions.values) validateFunAnnotations(fd)
    for (cd <- newSymbols.classes.values) validateClassAnnotations(cd)

    newSymbols
  }
}

trait Trimmer extends inox.transformers.TreeTransformer {
  override val s: tt.type = tt // to get `FunAbsOps` implicit class for `fa.isManuallyDefined` and `fa.isDropped`
  override val t: extraction.throwing.Trees
  val ctx: inox.Context
  implicit val symbols: s.Symbols

  val kept = MutableSet[Identifier]()

  def transform(syms: s.Symbols): t.Symbols = {
    val newFunctions = syms.functions.values.map(transform)
    val newClasses = syms.classes.values.map(transform)

    t.NoSymbols
      .withFunctions(newFunctions.toSeq.filter(fd => kept.contains(fd.id)))
      .withClasses(newClasses.toSeq.filter(cd => kept.contains(cd.id)))
  }

  def transform(cd: s.ClassDef): t.ClassDef = {
    new t.ClassDef(
      cd.id,
      cd.tparams.map(transform),
      cd.parents.map(transform).map(_.asInstanceOf[t.ClassType]),
      cd.fields.map(transform),
      cd.flags.map(transform)
    ).setPos(cd)
  }

  def transform(lfd: s.LocalFunDef): t.LocalFunDef = {
    val fa: s.FunAbstraction = s.Inner(lfd)
    if (fa.isManuallyDefined || fa.isDropped)
      new t.LocalFunDef(
        lfd.id,
        lfd.tparams.map(transform),
        lfd.params.map(transform),
        transform(lfd.returnType),
        transform(lfd.fullBody),
        lfd.flags.map(transform)
      ).setPos(lfd)
    else
      new t.LocalFunDef(
        lfd.id,
        lfd.tparams.map(transform),
        lfd.params.map(transform),
        transform(lfd.returnType),
        transform(lfd.fullBody),
        lfd.flags.map(transform)
      ).setPos(lfd)
  }

  override def transform(fd: s.FunDef): t.FunDef = {
    if (fd.isExported) kept += fd.id
    val ret = transform(fd.returnType)

    if (fd.isManuallyDefined || fd.isDropped)
      new t.FunDef(
        fd.id,
        fd.tparams.map(transform),
        fd.params.map(transform),
        ret,
        t.NoTree(ret),
        fd.flags.map(transform)
      ).setPos(fd)
    else
      new t.FunDef(
        fd.id,
        fd.tparams.map(transform),
        fd.params.map(transform),
        ret,
        transform(fd.fullBody),
        fd.flags.map(transform)
      ).setPos(fd)
  }

  override def transform(expr: s.Expr): t.Expr = expr match {
    case s.FunctionInvocation(id, _, _) =>
      kept += id
      super.transform(expr)

    case s.ClassConstructor(ct, _) =>
      val cd = symbols.getClass(ct.id)
      val rootId = root(ct.id)
      val rootCd = symbols.getClass(rootId)
      kept += ct.id
      kept += rootId
      kept ++= rootCd.descendants.map(_.id)
      super.transform(expr)

    case s.LetRec(lfds, body) =>
      t.LetRec(lfds.map(transform), transform(body))

    case _ => super.transform(expr)
  }
}

object TrimSymbols {
  def apply(implicit ctx: inox.Context): LeonPipeline[tt.Symbols, tt.Symbols] = new {
    val context = ctx
  } with TrimSymbols
}
