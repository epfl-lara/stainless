/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

// import purescala.Common.{ Identifier }
// import purescala.Definitions.{ ClassDef, Definition, FunDef, ModuleDef, Program }
// import purescala.DefOps.{ pathFromRoot }
// import purescala.{ TreeTraverser }

import extraction.throwing.trees._

import ExtraOps._

import collection.mutable.{Set => MutableSet}

/*
 * Compute the dependencies of the main function and its mandatory "_main" sibling.
 *
 * The list of dependencies includes "_main" but not "main" as the later is
 * annoted with @extern (cf. ExtractEntryPointPhase).
 *
 * Moreover, the list of dependencies only contains top level functions. For nested
 * functions, we need to compute their "context" (i.e. capture free variable) to
 * hoist them. This is done in a later phase. However, if a nested function uses
 * some type T, then T (and all its class hierarchy if T is a class) will be included
 * in the dependency set.
 *
 * This phase also make sure @cCode.drop function are not used. The same is *NOT*
 * done for dropped types as they might still be present in function signature. They
 * should be removed in a later (transformation) phase. Additionally, this phase
 * ensures that the annotation set on class and function is sane.
 *
 * NOTE We cannot rely on purescala.DependencyFinder as it will traverse functions
 *     annotated with @cCode.function and we don't want that. The same applies for
 *     classes annotated with @cCode.typdef. We therefore implement a simpler version
 *     of it here based on a TreeTraverser.
 */
private[genc] object ComputeDependenciesPhase
    extends LeonPipeline[(Symbols, Definition), Dependencies] {
  val name = "Dependency computer"
  val description = "Compute the dependencies of a given definition"

  def getTimer(ctx: inox.Context) = ctx.timers.genc.get("compute dependencies")

  var warned = false

  def run(ctx: inox.Context, input: (Symbols, Definition)): Dependencies = {
    implicit val (syms, entryPoint) = input

    implicit val printerOpts = PrinterOptions.fromContext(ctx)

    def validateClassAnnotations(cd: ClassDef): Unit = {

      val pos = cd.getPos

      if (cd.isManuallyTyped && cd.isDropped)
        ctx.reporter.fatalError(pos, s"${cd.id} cannot be both dropped and manually defined")

      if (cd.isGeneric && cd.isManuallyTyped)
        ctx.reporter.fatalError(
          pos,
          s"${cd.id} cannot be both a generic type and manually defined"
        )

      if (cd.isManuallyTyped && cd.parents.nonEmpty)
        ctx.reporter.fatalError(
          pos,
          s"${cd.id} cannot be manually defined because it is part of a class hierarchy"
        )

      if (cd.isRecursive)
        ctx.reporter.fatalError(pos, s"${cd.id} and other recursive types are not supported")
      if (!cd.isManuallyTyped) {
        if (cd.isRecursive)
          ctx.reporter.fatalError("Recursive types are not supported")
      }
    }

    def validateFunAnnotations(fd: FunDef): Unit = {
      val pos = fd.getPos

      // Those next three tests could be carried out on all functions, not just dependencies
      if (fd.isExtern && !fd.isManuallyDefined && !fd.isDropped)
        ctx.reporter.fatalError(
          pos,
          s"Extern functions (${fd.id.asString}) need to be either manually defined or dropped"
        )

      if (fd.isManuallyDefined && fd.isDropped)
        ctx.reporter.fatalError(
          pos,
          s"Functions (${fd.id.asString}) cannot be dropped and manually implemented at the same time"
        )

      if (fd.isGeneric && fd.isManuallyDefined)
        ctx.reporter.fatalError(
          pos,
          s"Functions (${fd.id.asString}) cannot be both a generic function and manually defined"
        )

      // This last test is specific to dependencies.
      if (fd.isDropped)
        ctx.reporter.fatalError(
          pos,
          s"Dropped functions (${fd.id.asString}) shall not be used"
        )
    }

    val finder = new ComputeDependenciesImpl(ctx)
    val deps = finder(entryPoint)

    // Ensure all annotations are sane on all dependencies, including nested functions.
    deps foreach {
      case fd: FunDef   => validateFunAnnotations(fd)
      case cd: ClassDef => validateClassAnnotations(cd)
      case _            => ()
    }

    Dependencies(syms, deps)
  }
}

// ComputeDependenciesImpl is agnostic to what should go or not in the dependency set;
// for example, nested functions will get registered. However, it will not traverse the body
// of function definition annotated with @cCode.function nor process fields of a @cCode.typedef
// class definition.
private final class ComputeDependenciesImpl(val ctx: inox.Context)(implicit
    val syms: Symbols
) extends SelfTreeTraverser {
  private val dependencies = MutableSet[Definition]()

  // Compute the dependencies of `entry`, which includes itself.
  def apply(entry: Definition): Set[Definition] = {
    entry match {
      case e: FunDef => traverse(e)
      case _ =>
        ctx.reporter.fatalError(
          s"unexpected type of entry point: ${entry.getClass}"
        )
    }

    dependencies.toSet
  }

  override def traverse(id: Identifier): Unit = {
    syms.lookupClass(id).foreach(traverse)
    syms.lookupFunction(id).foreach(traverse)
  }

  override def traverse(e: Expr): Unit = e match {
    // Don't traverse the local function definitions if they're manually defined
    case LetRec(lfds, body) if lfds.forall(Inner(_).isManuallyDefined) =>
      traverse(body)
    case _ => super.traverse(e)
  }

  override def traverse(cd: ClassDef): Unit = if (!dependencies(cd)) {
    dependencies += cd

    if (!cd.isManuallyTyped) {
      // Visit the whole class hierarchy with their fields, recursiverly
      cd.fields.foreach(traverse)
      for (tcd <- cd.ancestors) {
        traverse(tcd.cd)
        for (tcd2 <- tcd.descendants)
          traverse(tcd2.cd)
      }
      super.traverse(cd)
    }
  }

  override def traverse(fd: FunDef): Unit = if (!dependencies(fd)) {
    dependencies += fd

    if (!fd.isManuallyDefined) {
      // Visite return type, body & arguments
      traverse(fd.returnType)
      traverse(fd.fullBody)
      fd.params foreach { vd => traverse(vd.id) }
    }
  }

}
