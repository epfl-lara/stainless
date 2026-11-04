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
class TrimSymbols(using override val context: inox.Context) extends LeonPipeline[tt.Symbols, tt.Symbols](context) {
  val name = "Symbol trimmer"

  import context._

  def run(syms: tt.Symbols): tt.Symbols = {
    import syms.given
    given tt.PrinterOptions = tt.PrinterOptions.fromContext(context)

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

    val trim = new Trimmer(syms)
    val newSymbols = trim.transform(syms)

    for (fd <- newSymbols.functions.values) validateFunAnnotations(fd)
    for (cd <- newSymbols.classes.values) validateClassAnnotations(cd)

    newSymbols
  }
}

class Trimmer(override val s: tt.type, // to get `FunAbsOps` implicit class for `fa.isManuallyDefined` and `fa.isDropped`
              override val t: tt.type,
              override val symbols: tt.Symbols)
             (using val context: inox.Context) extends extraction.imperative.TransformerWithType {

  def this(symbols: tt.Symbols)(using inox.Context) =
    this(tt, tt, symbols)

  import symbols.given

  val kept = MutableSet[Identifier]()

  private def register(cid: Identifier): Unit = {
    val cd = symbols.getClass(cid)
    val rootId = root(cid)
    val rootCd = symbols.getClass(rootId)
    kept += cid
    kept += rootId
    kept ++= rootCd.descendants.map(_.id)
  }

  /** The definitions from which `Scala2IR` starts the translation, plus the field initializers of
   *  global classes, which `Scala2IR` reads to initialize global state.
   */
  private def isRoot(fd: s.FunDef): Boolean =
    fd.isExported ||
    fd.flags.exists(_.name == "cCode.define") ||
    fd.flags.exists {
      case s.ClassParamInit(cid) => symbols.lookupClass(cid).exists(_.isGlobal)
      case _ => false
    }

  private def isRoot(cd: s.ClassDef): Boolean =
    cd.isExported || cd.isGlobal

  /** Keeps only the symbols reachable from the roots: transforming a definition registers the
   *  symbols it mentions in `kept`, so definitions are transformed until no new symbol is reached.
   */
  def transform(syms: s.Symbols): t.Symbols = {
    kept ++= syms.functions.values.filter(isRoot).map(_.id)
    syms.classes.values.filter(isRoot).foreach(cd => register(cd.id))
    val visited = MutableSet[Identifier]()
    val newFunctions = collection.mutable.ArrayBuffer[t.FunDef]()
    val newClasses = collection.mutable.ArrayBuffer[t.ClassDef]()

    while (!kept.subsetOf(visited)) {
      for (id <- (kept -- visited).toSeq) {
        visited += id
        syms.lookupFunction(id).foreach(fd => newFunctions += transform(fd))
        syms.lookupClass(id).foreach(cd => newClasses += transform(cd))
      }
    }

    t.NoSymbols
      .withFunctions(newFunctions.toSeq)
      .withClasses(newClasses.toSeq)
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

  override def transform(tpe: s.Type): t.Type = tpe match {
    case ct: s.ClassType =>
      register(ct.id)
      super.transform(tpe)

    case _ => super.transform(tpe)
  }

  override def transform(expr: s.Expr, tpe: s.Type): t.Expr = expr match {
    case s.FunctionInvocation(id, _, _) =>
      kept += id
      super.transform(expr, tpe)

    case s.ClassConstructor(ct, _) =>
      register(ct.id)
      super.transform(expr, tpe)

    case s.LetRec(lfds, body) =>
      t.LetRec(lfds.map(transform), transform(body))

    case _ =>
      if (tpe.isInstanceOf[s.ClassType])
        register(tpe.asInstanceOf[s.ClassType].id)
      super.transform(expr, tpe)
  }
}
