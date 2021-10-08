/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import extraction._
import extraction.throwing. { trees => tt }

import genc.ExtraOps._

class GhostElimination(override val s: tt.type, // to use `isExported` from `genc.ExtraOps.FunDefOps`
                       override val t: throwing.Trees)
                      (val symbols: tt.Symbols,
                       val context: inox.Context) extends inox.transformers.Transformer {

  given sPrinterOptions: s.PrinterOptions = s.PrinterOptions.fromContext(context)

  case class Env(lfds: Map[Identifier, s.LocalFunDef])

  private def keepFlag(flag: s.Flag): Boolean =
    !flag.isInstanceOf[s.HasADTInvariant] &&
    flag != s.IsInvariant &&
    flag != s.InlineInvariant

  def transform(cd: s.ClassDef, env: Env): t.ClassDef = {
    new t.ClassDef(
      cd.id,
      cd.tparams.map(transform(_, env)),
      cd.parents.map(transform(_, env)).map(_.asInstanceOf[t.ClassType]),
      cd.fields.filterNot(_.flags.contains(s.Ghost)).map(transform(_, env)),
      cd.flags.filter(keepFlag).map(transform(_, env))
    ).setPos(cd)
  }

  def transform(cons: s.ADTConstructor, env: Env): t.ADTConstructor = {
    new t.ADTConstructor(
      cons.id,
      cons.sort,
      cons.fields.filterNot(_.flags.contains(s.Ghost)).map(transform(_, env)),
    ).setPos(cons)
  }

  def transform(sort: s.ADTSort, env: Env): t.ADTSort = {
    new t.ADTSort(
      sort.id,
      sort.tparams.map(transform(_, env)),
      sort.constructors.map(transform(_, env)),
      sort.flags.filter(keepFlag).map(transform(_, env))
    ).setPos(sort)
  }

  def transform(lfd: s.LocalFunDef, env: Env): t.LocalFunDef = {
    new t.LocalFunDef(
      lfd.id,
      lfd.tparams.map(transform(_, env)),
      lfd.params.filterNot(_.flags.contains(s.Ghost)).map(transform(_, env)),
      transform(lfd.returnType, env),
      transform(lfd.fullBody, env),
      lfd.flags.filter(keepFlag).map(transform(_, env))
    ).setPos(lfd)
  }

  def transform(fd: s.FunDef, env: Env): t.FunDef = {
    import s.exprOps._
    val specced = BodyWithSpecs(fd.fullBody)
    val body = if (fd.isExported)
      specced.specs.foldRight(specced.body) {
        case (spec @ LetInSpec(vd, e), acc) => s.Let(vd, e, acc).setPos(spec)
        case (spec @ Precondition(s.Annotated(cond, flags)), acc) if flags.contains(s.Ghost) => acc
        case (spec @ Precondition(cond), acc) => s.Assert(cond, Some("Dynamic precondition check"), acc).setPos(spec)
        case (_, acc) => acc
      }
    else
      specced.letsAndBody

    new t.FunDef(
      fd.id,
      fd.tparams.map(transform(_, env)),
      fd.params.filterNot(_.flags.contains(s.Ghost)).map(transform(_, env)),
      transform(fd.returnType, env),
      transform(body, env),
      fd.flags.filter(keepFlag).map(transform(_, env))
    ).setPos(fd)
  }

  override def transform(expr: s.Expr, env: Env): t.Expr = expr match {
    case fi: s.FunctionInvocation =>
      val fd = symbols.getFunction(fi.id)
      if (fd.flags.contains(s.Ghost)) {
        context.reporter.fatalError(fi.getPos, s"Unexpected invocation to ghost function ${fd.id}")
      } else {
        val filteredArgs = fi.args.zip(fd.params).filter {
          case (arg, vd) => !vd.flags.contains(s.Ghost)
        }.map(_._1).map(transform(_, env))
        t.FunctionInvocation(fi.id, fi.tps.map(transform(_, env)), filteredArgs)
      }

    case s.ApplyLetRec(id, tparams, tpe, tps, args) =>
      val lfd = env.lfds(id)
      val nonGhostArgs = args.zip(lfd.params).filter(!_._2.flags.contains(s.Ghost)).map(_._1)
      t.ApplyLetRec(id, tparams.map(_.asInstanceOf[t.TypeParameter]), transform(tpe, env).asInstanceOf[t.FunctionType], tps.map(transform(_, env)), nonGhostArgs.map(transform(_, env)))

    case s.ClassConstructor(ct, args) =>
      val cd = symbols.getClass(ct.id)
      val nonGhostArgs = args.zip(cd.fields).filter(!_._2.flags.contains(s.Ghost)).map(_._1)
      t.ClassConstructor(transform(ct, env).asInstanceOf[t.ClassType], nonGhostArgs.map(transform(_, env)))

    case s.Let(vd, e, body) if vd.flags.contains(s.Ghost) => transform(body, env)

    case s.Assert(s.Annotated(_, flags), _, body) if flags.contains(s.Ghost) => transform(body, env)

    case s.LetRec(lfds, body) =>
      val nonGhostLfds = lfds.filterNot(_.flags.contains(s.Ghost))
      val newEnv = env.copy(lfds = env.lfds ++ nonGhostLfds.map(lfd => lfd.id -> lfd))
      t.LetRec(nonGhostLfds.map(transform(_, newEnv)), transform(body, newEnv))

    case s.Block(es, last) => t.Block(es.filterNot {
      case fi: s.FunctionInvocation if symbols.getFunction(fi.id).flags.contains(s.Ghost) => true
      case fi: s.FunctionInvocation =>
        val fd = symbols.getFunction(fi.id)
        fd.id.name == "ghost" && fd.params.length == 1 && fd.params.head.flags.contains(s.Ghost)
      case _ => false
    }.map(transform(_, env)), transform(last, env))

    case s.While(cond, body, _, _, flags) => t.While(transform(cond, env), transform(body, env), None, None, flags.map(transform(_, env)))

    case _ => super.transform(expr, env)

  }

  def transform(symbols: s.Symbols): t.Symbols = {
    val emptyEnv = Env(Map())
    t.NoSymbols
      .withFunctions(symbols.functions.values.toSeq.filterNot(fd => fd.flags.contains(s.Ghost) || fd.flags.contains(s.IsInvariant)).map(transform(_, emptyEnv)))
      .withSorts(symbols.sorts.values.toSeq.map(transform(_, emptyEnv)))
      .withClasses(symbols.classes.values.toSeq.map(transform(_, emptyEnv)))
  }

}

class GhostEliminationPhase(using override val context: inox.Context) extends LeonPipeline[tt.Symbols, tt.Symbols](context) {
  val name = "Ghost Code Elimination"

  given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC
  import tt._

  def run(syms: Symbols): Symbols = {
    class Impl(override val s: tt.type, override val t: tt.type)
      extends GhostElimination(s, t)(syms, context)
    val ge = new Impl(tt, tt)
    ge.transform(syms)
  }
}
