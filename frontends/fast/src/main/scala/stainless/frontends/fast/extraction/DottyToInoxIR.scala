package stainless.frontends.fast.extraction

import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.ast.untpd
import dotty.tools.dotc.ast.untpd.InfixOp
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.StdNames.nme
import dotty.tools.dotc.core.{Constants, Flags, Names}
import dotty.tools.dotc.util.Positions.Position
import stainless.frontends.dotc.SymbolsContext
import stainless.frontends.fast.IRs
import stainless.{FreshIdentifier, Identifier}

import scala.language.implicitConversions

trait DottyToInoxIR
  extends ExtractMods {
  self: IRs =>

  private case class DefContext(
                                 localVars: Set[Identifiers.Identifier] = Set.empty,
                                 isExtern: Boolean = false
                               ) {
    def union(that: DefContext): DefContext = {
      copy(this.localVars ++ that.localVars,
        this.isExtern || that.isExtern)
    }

    def isVariable(ident: Identifiers.Identifier): Boolean = localVars contains ident

    def withNewLocalVar(localVar: Identifiers.Identifier): DefContext =
      copy(this.localVars + localVar, isExtern)

    def withNewLocalVars(vars: Traversable[Identifiers.Identifier]): DefContext =
      copy(this.localVars ++ vars, isExtern)
  }


  private val Int8Type = Types.Primitives.BVType(8)
  private val Int16Type = Types.Primitives.BVType(16)
  private val Int32Type = Types.Primitives.BVType(32)


  implicit def dottyPosToParserCombinatorPos(p: Position)(implicit ctx: Context): scala.util.parsing.input.Position =
    scala.util.Try({
      if (!p.exists) {
        scala.util.parsing.input.NoPosition
      } else {
        scala.util.parsing.input.OffsetPosition(ctx.source.toString(), p.start)
      }
    }).toOption.getOrElse(scala.util.parsing.input.NoPosition)


//  def outOfSubsetError(pos: Position, msg: String)(implicit ctx: Context): Nothing =
//    throw new frontend.UnsupportedCodeException(dottyPosToParserCombinatorPos(pos), msg)
//
//  def outOfSubsetError(t: untpd.Tree, msg: String)(implicit ctx: Context): Nothing = outOfSubsetError(t.pos, msg)


  def extractRef(t: untpd.RefTree)(implicit inoxCtx: inox.Context, cache: SymbolsContext, ctx: Context): Identifier = {
    def rec(t: untpd.Tree): Seq[String] = t match {
      case Select(t2, name) => rec(t2) :+ name.toString
      case Ident(name) => Seq(name.toString)
      case untpd.EmptyTree => Seq.empty
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

  def extractBinding(valDef: untpd.ValDef)(implicit ctx: Context): Bindings.Binding = extractType(valDef.tpt) match {
    case Some(tpe) => Bindings.ExplicitValDef(Identifiers.IdentifierName(valDef.name.toString), tpe).setPos(valDef.pos)
    case _ => Bindings.InferredValDef(Identifiers.IdentifierName(valDef.name.toString)).setPos(valDef.pos)
  }

  def extractBindings(valDefs: Seq[untpd.ValDef])(implicit ctx: Context): Bindings.BindingSeq =
    HSeq.fromSeq(valDefs.map(valDef => extractBinding(valDef)))

  def mapNameToType(name: Names.Name): Types.Type = name.toString match {
    case "Int" => Types.Primitive(Int32Type)
    case "Boolean" => Types.Primitive(Types.Primitives.BooleanType)
    case "Short" => Types.Primitive(Int16Type)
    case "Byte" => Types.Primitive(Int8Type)
    case "Long" => Types.Primitive(Types.Primitives.IntegerType)
    case "Real" => Types.Primitive(Types.Primitives.RealType)
    case "String" => Types.Primitive(Types.Primitives.StringType)
    case "Unit" => Types.Primitive(Types.Primitives.UnitType)
    case _ => throw new Exception("Type could not be mapped:" + name.toString)
  }

  def extractType(tpe: untpd.Tree)(implicit ctx: Context): Option[Types.Type] = tpe match {
    case Ident(name) => Some(mapNameToType(name).setPos(tpe.pos))
    case untpd.Function(args, body) =>
      Some(Types.FunctionType(HSeq.fromSeq(args.map(extractType(_).get)), extractType(body).get))
    case _: untpd.TypeTree => None
    case _ => throw new Exception(tpe.toString)
  }

  def makeInfixOp(op: untpd.Ident, left: untpd.Tree, right: untpd.Tree)
                 (implicit ctx: Context, dctx: DefContext): Exprs.Expr = op.name.toString match {
    case "+" => Exprs.BinaryOperation(Exprs.Binary.Plus,
      extractExpression(left), extractExpression(right))
    case "-" => Exprs.BinaryOperation(Exprs.Binary.Minus,
      extractExpression(left), extractExpression(right))
    case "/" => Exprs.BinaryOperation(Exprs.Binary.Division,
      extractExpression(left), extractExpression(right))
    case "*" => Exprs.BinaryOperation(Exprs.Binary.Times,
      extractExpression(left), extractExpression(right))
    case "%" => Exprs.BinaryOperation(Exprs.Binary.Modulo,
      extractExpression(left), extractExpression(right))
    case "<" => Exprs.BinaryOperation(Exprs.Binary.LessThan,
      extractExpression(left), extractExpression(right))
    case "<=" => Exprs.BinaryOperation(Exprs.Binary.LessEquals,
      extractExpression(left), extractExpression(right))
    case ">" => Exprs.BinaryOperation(Exprs.Binary.GreaterThan,
      extractExpression(left), extractExpression(right))
    case ">=" => Exprs.BinaryOperation(Exprs.Binary.GreaterEquals,
      extractExpression(left), extractExpression(right))
    case "==" => Exprs.BinaryOperation(Exprs.Binary.Equals,
      extractExpression(left), extractExpression(right))
    case "||" => Exprs.NaryOperation(Exprs.NAry.Or,
      HSeq.fromSeq(Seq(extractExpression(left), extractExpression(right))))
    case "&&" => Exprs.NaryOperation(Exprs.NAry.And,
      HSeq.fromSeq(Seq(extractExpression(left), extractExpression(right))))
    case "==>" => Exprs.NaryOperation(Exprs.NAry.Or,
      HSeq.fromSeq(Seq(
        Exprs.UnaryOperation(Exprs.Unary.Not, extractExpression(left)), extractExpression(right))))
  }

  def makePrefixOp(op: untpd.Ident, body: untpd.Tree)
                  (implicit ctx: Context, dctx: DefContext): Exprs.UnaryOperation = op.name.toString match {
    case "-" => Exprs.UnaryOperation(Exprs.Unary.Minus, extractExpression(body))
    case "!" => Exprs.UnaryOperation(Exprs.Unary.Not, extractExpression(body))
    case "~" => Exprs.UnaryOperation(Exprs.Unary.BVNot, extractExpression(body))
  }

  def extractBigIntValue(tree: untpd.Tree): BigInt = tree match {
    case Literal(const) =>
      const.tag match {
        case Constants.IntTag => const.intValue
        case Constants.ShortTag => const.intValue
        case Constants.ByteTag => const.intValue
        case Constants.LongTag => const.longValue
      }
  }

  def extractExpression(rhs: untpd.Tree)(implicit ctx: Context, dctx: DefContext): Exprs.Expr = (rhs match {
    case Ident(name) =>
      val identifier = Identifiers.IdentifierName(name.toString.trim).setPos(rhs.pos)
      if (dctx.isVariable(identifier))
        Exprs.Variable(identifier).setPos(rhs.pos)
      else
        Exprs.Invocation(identifier, None, HSeq.fromSeq(Seq.empty[Exprs.Expr])).setPos(rhs.pos)
    case Apply(Ident(name), args) if name.toString == "Real" && args.length <= 2 && args.nonEmpty=>
      args.length match {
        case 1 => Exprs.FractionLiteral(extractBigIntValue(args.head), 1)
        case 2 => Exprs.FractionLiteral(extractBigIntValue(args.head), extractBigIntValue(args(1)))
      }

    case Literal(const) =>
      const.tag match {
        case Constants.IntTag | Constants.ByteTag | Constants.ShortTag | Constants.LongTag =>
          Exprs.IntegerLiteral(const.intValue)
        case Constants.BooleanTag =>
          Exprs.BooleanLiteral(const.booleanValue)
      }
    case InfixOp(left, op, right) =>
      makeInfixOp(op, left, right).setPos(dottyPosToParserCombinatorPos(rhs.pos))
    case untpd.PrefixOp(op, body) =>
      makePrefixOp(op, body)
    case Apply(fun: untpd.Ident, args) =>
      Exprs.Invocation(Identifiers.IdentifierName(fun.name.toString), None, HSeq.fromSeq(args.map(extractExpression(_))))

    case If(cond, thenBranch, elseBranch) =>
      Exprs.If(extractExpression(cond), extractExpression(thenBranch), extractExpression(elseBranch))
    case untpd.Parens(expr) =>
      extractExpression(expr)
  }).setPos(rhs.pos)

  def processBody(stats: List[Tree[Untyped]], expr: untpd.Tree)(implicit ctx: Context, dctx: DefContext): Exprs.Expr = {
    def rec(stats: List[untpd.Tree]): Exprs.Expr = stats match {
      case (head:untpd.ValDef) :: Nil =>
        Exprs.Let(extractBinding(head), extractExpression(head.rhs),
          extractExpression(expr)).setPos(head.pos)
      case (head:untpd.ValDef) :: tail =>
        Exprs.Let(extractBinding(head), extractExpression(head.rhs),
          rec(tail)).setPos(head.pos)
      case Nil => extractExpression(expr)
    }
    rec(stats)
  }

  def extractBody(body: untpd.Tree)(implicit ctx: Context, dctx: DefContext): Exprs.Expr = body match {
    case block: untpd.Block => processBody(block.stats, block.expr)
    case _ => extractExpression(body)
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
            case vd: untpd.ValDef if !mods.is(Flags.CaseAccessor) && !mods.is(Flags.ParamAccessor) &&
              !mods.is(Flags.Synthetic) && !mods.is(Flags.Mutable) =>
              result = result :+
                Right(Function(Identifiers.IdentifierName(vd.name.toString),
                  HSeq.fromSeq(Seq.empty[Identifiers.Identifier]), HSeq.fromSeq(Seq.empty[Bindings.Binding]),
                  extractType(vd.tpt), extractBody(vd.rhs)(ctx, DefContext())).setPos(stat.pos))

            case module: untpd.ModuleDef if (mods.flags.is(Flags.ModuleClass) || mods.flags.is(Flags.Package))
              && !mods.flags.is(Flags.Synthetic) && !mods.flags.is(Flags.Case) =>
              result ++= extractObject(module)

            case f@ExFunctionDef(name, typeParams, valDefs, returnType, body) =>
              val bindings = extractBindings(valDefs)
              val parameterIdentifiers = bindings.elems.map {
                case Right(binding: Bindings.InferredValDef) => binding.identifier
                case Right(binding: Bindings.ExplicitValDef) => binding.identifier
              }.toSet
              result = result :+
                Right(Function(Identifiers.IdentifierName(name.toString), extractTypeParams(typeParams),
                  extractBindings(valDefs), extractType(returnType),
                  extractBody(body)(ctx, DefContext(parameterIdentifiers))).setPos(stat.pos))
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
