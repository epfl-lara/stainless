package stainless.frontends.fast.extraction

import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.ast.untpd
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.StdNames.nme
import dotty.tools.dotc.core.{Contexts, Flags, Names}
import dotty.tools.dotc.util.Positions.Position
import stainless.frontends.dotc.SymbolsContext
import stainless.{FreshIdentifier, Identifier, frontend}
import stainless.frontends.fast.IRs

import scala.language.implicitConversions

trait DottyToInoxIR
  extends ExtractMods {
  self: IRs =>

  private val Int8Type = Types.Primitives.BVType(8)
  private val Int16Type = Types.Primitives.BVType(16)
  private val Int32Type = Types.Primitives.BVType(32)

  implicit def dottyPosToInoxPos(p: Position)(implicit ctx: Context): inox.utils.Position = scala.util.Try({
    if (!p.exists) {
      inox.utils.NoPosition
    } else if (p.start != p.end) {
      val start = ctx.source.atPos(p.startPos)
      val end = ctx.source.atPos(p.endPos)
      inox.utils.RangePosition(start.line + 1, start.column + 1, start.point,
        end.line + 1, end.column + 1, end.point,
        ctx.source.file.file)
    } else {
      val sp = ctx.source.atPos(p)
      inox.utils.OffsetPosition(sp.line + 1, sp.column + 1, sp.point,
        ctx.source.file.file)
    }
  }).toOption.getOrElse(inox.utils.NoPosition)


  def outOfSubsetError(pos: Position, msg: String)(implicit ctx: Context): Nothing =
    throw new frontend.UnsupportedCodeException(dottyPosToInoxPos(pos), msg)

  def outOfSubsetError(t: untpd.Tree, msg: String)(implicit ctx: Context): Nothing = outOfSubsetError(t.pos, msg)


  def extractRef(t: untpd.RefTree)(implicit inoxCtx: inox.Context, cache: SymbolsContext, ctx: Context): Identifier = {
    def rec(t: untpd.Tree): Seq[String] = t match {
      case Select(t2, name) => rec(t2) :+ name.toString
      case Ident(name) => Seq(name.toString)
      case untpd.EmptyTree => Seq.empty
      case _ => outOfSubsetError(t, "Unexpected selector " + t)
    }

    val refs = (rec(t.qualifier) :+ t.name.toString).filter(_ != "<empty>")
    FreshIdentifier(refs.mkString("$"))
  }

  import Functions._

  def extractObject(module: untpd.ModuleDef)
                   (implicit inoxCtx: inox.Context, cache: SymbolsContext, ctx: Context):
  Seq[Either[ADTs.Sort, Function]] = {
    val template = module.impl
    // TODO missing inheritance check
    extractStatic(template.body)
  }

  def extractTypeParams(typeParams: Seq[untpd.TypeDef]): Identifiers.IdentifierSeq =
    HSeq.fromSeq(typeParams.map(tree => Identifiers.IdentifierName(tree.name.toString())))

  def extractBinding(valDef: untpd.ValDef): Bindings.Binding = extractType(valDef.tpt) match {
    case Some(tpe) => Bindings.ExplicitValDef(Identifiers.IdentifierName(valDef.name.toString), tpe)
    case _ => Bindings.InferredValDef(Identifiers.IdentifierName(valDef.name.toString))
  }

  def extractBindings(valDefs: Seq[untpd.ValDef]): Bindings.BindingSeq =
    HSeq.fromSeq(valDefs.map(valDef => extractBinding(valDef)))

  def mapNameToType(name: Names.Name): Types.Type = name.toString match {
    case "Int" => Types.Primitive(Int32Type)
    case "Boolean" => Types.Primitive(Types.Primitives.BooleanType)
    case "Short" => Types.Primitive(Int16Type)
    case "Byte" => Types.Primitive(Int8Type)
    case _ => throw new Exception("Type could not be mapped:" + name.toString)
  }

  def extractType(tpe: untpd.Tree): Option[Types.Type] = tpe match {
    case Ident(name) => Some(mapNameToType(name))
    case _ => throw new Exception(tpe.toString)
  }

  def extractExpression(rhs: untpd.Tree): Exprs.Expr = rhs match {
    case Ident(name) => Exprs.Variable(Identifiers.IdentifierName(name.toString))
  }

  def makeContext(expr: untpd.Tree)(implicit ctx: Context): Exprs.Expr => Exprs.Expr = expr match {
    case valDef: untpd.ValDef => body => Exprs.Let(extractBinding(valDef), extractExpression(valDef.rhs), body)
    case _ => throw new Exception("Processing body of the function, got something different than val def")
  }

  def processBody(stats: List[Tree[Untyped]], expr: Exprs.Expr)(implicit ctx: Context): Exprs.Expr = {
    def rec(stats: List[untpd.Tree], context: Exprs.Expr => Exprs.Expr): Exprs.Expr = stats match {
      case head::Nil => makeContext(head)(ctx)(expr)
      case head::tail => context(rec(tail, makeContext(head)))
      case Nil => expr
    }
    rec(stats, t => t)
  }

  def extractBody(body: untpd.Tree)(implicit ctx: Context): Exprs.Expr = body match {
    case block: untpd.Block => processBody(block.stats, extractExpression(block.expr))
    case _ => throw new Exception(body.toString)
  }

  /**
    * Extracts static currently no classes, no modules, no classes and no imports
    * How to model modules in the current implementation
    *
    * @param stats
    * @return
    */
  def extractStatic(stats: List[untpd.Tree])
                   (implicit inoxCtx: inox.Context, cache: SymbolsContext, ctx: Context):
  Seq[Either[ADTs.Sort, Function]] = {
    var result: Seq[Either[ADTs.Sort, Function]] = Seq()

    for (stat <- stats) stat match {
      case untpd.EmptyTree =>
      // ignore untyped trees
      case t: untpd.MemberDef =>
        val mods = extractMods(t)
        if (mods.flags.is(Flags.Synthetic))
        //ignore
          Unit
        else
          t match {
            case vd@ValDef(_, _, _) if mods.flags.is(Flags.Module) =>
            //ignore
            case module: untpd.ModuleDef if (mods.flags.is(Flags.ModuleClass) || mods.flags.is(Flags.Package))
              && !mods.flags.is(Flags.Synthetic) && !mods.flags.is(Flags.Case) =>
              result ++= extractObject(module)
            case f@ExFunctionDef(name, typeParams, valDefs, returnType, body) =>
              Functions.Function(Identifiers.IdentifierName(name.toString), extractTypeParams(typeParams),
                extractBindings(valDefs), extractType(returnType), extractBody(body))
          }
    }

    result
  }

  object ExFunctionDef {
    def unapply(dd: untpd.DefDef)(implicit ctx: Context): Option[(Names.TermName, Seq[untpd.TypeDef], Seq[untpd.ValDef], untpd.Tree, untpd.Tree)] = {
      val mods = extractMods(dd)
      dd match {
        case DefDef(name, tparams, vparamss, tpt, rhs) =>
          if (name != nme.CONSTRUCTOR &&
            !mods.flags.is(Flags.Accessor) &&
            !mods.flags.is(Flags.Synthetic) &&
            !mods.flags.is(Flags.Label)) {
            Some((name, tparams, vparamss.flatten, tpt, dd.rhs))
          } else {
            None
          }

        case _ => None
      }
    }
  }

}
