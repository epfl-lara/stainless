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
 * Compute the dependencies of the @export functions
 * Generic functions cannot be marked @export (only specialized versions that are
 * used by exported functions are exported to C).
 *
 * Moreover, the list of dependencies only contains top level functions. For nested
 * functions, we need to compute their "context" (i.e. capture free variable) to
 * hoist them. This is done in a later phase. However, if a nested function uses
 * some type T, then T (and all its class hierarchy if T is a class) will be included
 * in the dependency set.
 *
 * This phase also make sures @cCode.drop functions are not used. The same is *NOT*
 * done for dropped types as they might still be present in function signature. They
 * should be removed in a later (transformation) phase. Additionally, this phase
 * ensures that the annotation set on class and function is sane.
 *
 * NOTE We cannot rely on purescala.DependencyFinder as it will traverse functions
 *     annotated with @cCode.function and we don't want that. The same applies for
 *     classes annotated with @cCode.typdef. We therefore implement a simpler version
 *     of it here based on a TreeTraverser.
 */
trait ComputeDependenciesPhase extends LeonPipeline[Symbols, Dependencies] {
  val name = "Dependency computer"

  implicit val context: inox.Context
  import context._

  def run(syms: Symbols): Dependencies = {
    implicit val symbols = syms
    implicit val printerOpts = PrinterOptions.fromContext(context)

    def validateClassAnnotations(cd: ClassDef): Unit = {

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

    def validateFunAnnotations(fd: FunDef): Unit = {
      val pos = fd.getPos

      // Those next three tests could be carried out on all functions, not just dependencies
      if (fd.isExtern && !fd.isManuallyDefined && !fd.isDropped)
        reporter.fatalError(
          pos,
          s"Extern functions (${fd.id.asString}) need to be either manually defined or dropped"
        )

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

      // This last test is specific to dependencies.
      if (fd.isDropped)
        reporter.fatalError(
          pos,
          s"Dropped functions (${fd.id.asString}) shall not be used"
        )
    }

    val finder = new ComputeDependenciesImpl(context)
    val exportedObjects: Seq[Definition] =
      syms.functions.values.toSeq.filter(_.isExported) ++
      syms.classes.values.toSeq.filter(_.isExported)

    val deps = finder(exportedObjects)

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
) extends SelfTraverser {
  private val dependencies = MutableSet[Definition]()

  case class Env(m: Map[Identifier, LocalFunDef]) {
    def withLocals(fds: Seq[LocalFunDef]): Env =
      Env(m ++ fds.map(fd => fd.id -> fd))
  }

  // Compute the dependencies of `entry`, which includes itself.
  def apply(exported: Seq[Definition]): Set[Definition] = {
    exported.foreach(traverseDef)
    dependencies.toSet
  }

  private def traverseDef(df: Definition): Unit = df match {
    case fd: FunDef => traverse(fd, Env(Map()))
    case cd: ClassDef => traverse(cd, Env(Map()))
    case _ => ctx.reporter.fatalError(s"ComputeDependenciesPhase cannot traverse ${df.id} (${df.getClass})")
  }

  override def traverse(id: Identifier, env: Env): Unit = {
    syms.lookupClass(id).foreach(traverse(_, env))
    syms.lookupFunction(id).foreach(traverse(_, env))
  }

  override def traverse(e: Expr, env: Env): Unit = e match {
    // Don't traverse the local function definitions if they're manually defined
    case LetRec(lfds, body) if lfds.forall(Inner(_).isManuallyDefined) =>
      val newEnv = env.withLocals(lfds)
      traverse(body, newEnv)

    // Don't traverse the local function definitions if they're manually defined
    case LetRec(lfds, body) =>
      val newEnv = env.withLocals(lfds)
      super.traverse(e, newEnv)

    // Don't traverse ghost function arguments
    case FunctionInvocation(id, tps, args) =>
      traverse(id, env)
      tps.foreach(traverse(_, env))
      val fd = syms.getFunction(id)
      val nonGhostArgs = args.zip(fd.params).filter(!_._2.flags.contains(Ghost)).map(_._1)
      nonGhostArgs.foreach(traverse(_, env))

    // Don't traverse ghost function arguments
    case ApplyLetRec(id, tparams, tpe, tps, args) =>
      traverse(id, env)
      tparams.foreach(traverse(_, env))
      traverse(tpe, env)
      tps.foreach(traverse(_, env))
      val lfd = env.m(id)
      val nonGhostArgs = args.zip(lfd.params).filter(!_._2.flags.contains(Ghost)).map(_._1)
      nonGhostArgs.foreach(traverse(_, env))

    // Don't traverse ghost class fields
    case ClassConstructor(ct, args) =>
      val cd = syms.getClass(ct.id)
      val nonGhostArgs = args.zip(cd.fields).filter(!_._2.flags.contains(Ghost)).map(_._1)
      traverse(ct, env)
      nonGhostArgs.foreach(traverse(_, env))

    case _ =>
      super.traverse(e, env)
  }

  def traverse(cd: ClassDef, env: Env): Unit = if (!dependencies(cd)) {
    dependencies += cd

    if (!cd.isManuallyTyped) {
      // Visit the whole class hierarchy with their fields, recursiverly
      cd.fields.filter(!_.flags.contains(Ghost)).foreach(traverse(_, env))
      for (tcd <- cd.ancestors) {
        traverse(tcd.cd, env)
        for (tcd2 <- tcd.descendants)
          traverse(tcd2.cd, env)
      }
      // Visit the parameters initializers
      syms.paramInits(cd.id).foreach(traverse(_, env))
    }
  }

  def traverse(fd: FunDef, env: Env): Unit = if (!dependencies(fd)) {
    dependencies += fd

    if (!fd.isManuallyDefined) {
      // Visite return type, body & non-ghost arguments
      traverse(fd.returnType, env)
      traverse(fd.fullBody, env)
      fd.params.filter(!_.flags.contains(Ghost)) foreach { vd =>
        traverse(vd, env)
      }
    }
  }

}

object ComputeDependenciesPhase {
  def apply(implicit ctx: inox.Context): LeonPipeline[Symbols, Dependencies] = new {
    val context = ctx
  } with ComputeDependenciesPhase
}
