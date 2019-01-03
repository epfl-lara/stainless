package stainless.frontends.fast.extraction

import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.ast.untpd
import dotty.tools.dotc.ast.untpd.InfixOp
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Names.Name
import dotty.tools.dotc.core.StdNames.nme
import dotty.tools.dotc.core.{Constants, Flags, Names}
import dotty.tools.dotc.util.Positions.Position
import stainless.frontends.dotc.SymbolsContext
import stainless.frontends.fast.IRs
import stainless.frontends.fast.irs.{PatternMatching, StainlessExprs}
import stainless.{FreshIdentifier, Identifier, frontend}

import scala.language.implicitConversions

trait DottyToInoxIR
  extends ExtractMods with PatternMatching with StainlessExprs {
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


  private val Int8Type = Types.Primitives.BVType(signed = true, 8)
  private val Int16Type = Types.Primitives.BVType(signed = true, 16)
  private val Int32Type = Types.Primitives.BVType(signed = true, 32)


  implicit def dottyPosToParserCombinatorPos(p: Position)(implicit ctx: Context): scala.util.parsing.input.Position =
    scala.util.Try({
      if (!p.exists) {
        scala.util.parsing.input.NoPosition
      } else {
        scala.util.parsing.input.OffsetPosition(ctx.source.toString(), p.start)
      }
    }).toOption.getOrElse(scala.util.parsing.input.NoPosition)


  implicit def dottyPosToInoxPos(p: Position)(implicit ctx: Context): inox.utils.Position = scala.util.Try({
    if (!p.exists) {
      inox.utils.NoPosition
    } else if (p.start != p.end) {
      val start = ctx.source.atPos(p.startPos)
      val end   = ctx.source.atPos(p.endPos)
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

  def extractTypeParams(typeParams: Seq[untpd.TypeDef])(implicit ctx: Context): Identifiers.IdentifierSeq =
    HSeq.fromSeq(typeParams.map(tree => Identifiers.IdentifierName(tree.name.toString()).setPos(tree.pos)))

  def extractBinding(valDef: untpd.ValDef)(implicit ctx: Context): Bindings.Binding = (extractType(valDef.tpt) match {
    case Some(tpe) => Bindings.ExplicitValDef(Identifiers.IdentifierName(valDef.name.toString), tpe)
    case _ => Bindings.InferredValDef(Identifiers.IdentifierName(valDef.name.toString))
  }).setPos(valDef.pos)

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
    case "BigInt" => Types.Primitive(Types.Primitives.IntegerType)
    case "Char" => Types.Primitive(Types.Primitives.CharType)
    case typeVariable => Types.Variable(Identifiers.IdentifierName(typeVariable))
  }

  def extractType(tpe: untpd.Tree)(implicit ctx: Context): Option[Types.Type] = tpe match {
    case Ident(name) => Some(mapNameToType(name).setPos(tpe.pos))
    case untpd.Function(args, body) =>
      Some(Types.FunctionType(HSeq.fromSeq(args.map(extractType(_).get.setPos(tpe.pos))), extractType(body).get.setPos(body.pos)))
    case untpd.Tuple(list) => Some(Types.TupleType(extractTypeArgs(list).get).setPos(tpe.pos))
    case AppliedTypeTree(Ident(name), list) if name.toString == "Set" =>
      Some(Types.Operation(Types.Operators.Set, extractTypeArgs(list).get).setPos(tpe.pos))
    case AppliedTypeTree(Ident(name), list) if name.toString == "Bag" =>
      Some(Types.Operation(Types.Operators.Bag, extractTypeArgs(list).get).setPos(tpe.pos))
    case AppliedTypeTree(Ident(name), list) if name.toString == "Map" =>
      Some(Types.Operation(Types.Operators.Map, extractTypeArgs(list).get).setPos(tpe.pos))
    case _: untpd.TypeTree => None
    case _ => throw new Exception(tpe.toString)
  }

  def extractTypeArgs(targs: List[untpd.Tree])(implicit ctx: Context): Option[Types.TypeSeq] = {
    def rec(list: List[untpd.Tree]): List[Types.Type] = list match {
      case head :: tail => extractType(head).get :: rec(tail)
      case Nil => Nil
    }
    rec(targs) match {
      case Nil => None
      case a => Some(HSeq.fromSeq(a))
    }
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
    case "++" => Exprs.BinaryOperation(StainlessExprs.AdditionalOperators.Union,
      extractExpression(left), extractExpression(right))
    case "&" => Exprs.BinaryOperation(Exprs.Binary.BVAnd, extractExpression(left), extractExpression(right))
    case "contains" => Exprs.BinaryOperation(StainlessExprs.AdditionalOperators.Contains,
      extractExpression(left), extractExpression(right))
    case "--" => Exprs.BinaryOperation(StainlessExprs.AdditionalOperators.Difference,
      extractExpression(left), extractExpression(right))
    case "updated" => Exprs.BinaryOperation(StainlessExprs.AdditionalOperators.Updated,
      extractExpression(left), extractExpression(right))
    case "subsetOf" => Exprs.PrimitiveInvocation(Exprs.Primitive.Subset, None,
      HSeq.fromSeq(Seq(extractExpression(left), extractExpression(right))))
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

  def extractPairs(value: untpd.Tree)(implicit ctx: Context, dctx: DefContext): Exprs.Pair = value match {
    case untpd.Tuple(trees) if trees.length == 2 => Exprs.Pair(extractExpression(trees.head), extractExpression(trees(1)))
    case InfixOp(left, op, right) if op.name.toString == "->"=>
      Exprs.Pair(extractExpression(left), extractExpression(right))
    case _ => outOfSubsetError(value, "Trying to extract a pair")
  }

  def extractPattern(pat: Tree[Untyped])(implicit ctx: Context, dctx: DefContext): PatternMatchings.Pattern = pat match {
    case Literal(_) => PatternMatchings.LiteralPattern(None, extractExpression(pat).asInstanceOf[Exprs.Expr with Exprs.Literal])
    case Bind(name, v: untpd.Literal) =>
      PatternMatchings.LiteralPattern(
        Some(Bindings.InferredValDef(Identifiers.IdentifierName(name.toString))),
        extractExpression(v).asInstanceOf[Exprs.Expr with Exprs.Literal])
    case Bind(name, Apply(Ident(fun), args)) =>
      val opt = if (name.toString == "_") Some(Bindings.InferredValDef(Identifiers.IdentifierName(name.toString))) else None
      PatternMatchings.CompoundTypePattern(opt, Identifiers.IdentifierName(fun.toString), Seq.empty, args.map(extractPattern(_)))
    case Bind(name, untpd.Tuple(list)) =>
      PatternMatchings.TuplePattern(Some(Bindings.InferredValDef(Identifiers.IdentifierName(name.toString))),
        list.map(extractPattern(_)))
    case Typed(Ident(name), tpt) =>
      PatternMatchings.InstanceOf(
        Some(Bindings.InferredValDef(Identifiers.IdentifierName(name.toString))), extractType(tpt).get)
    case Ident(name) if name.toString == "_" => PatternMatchings.WildcardPattern(None)
    case Ident(name) =>
      PatternMatchings.WildcardPattern(Some(Bindings.InferredValDef(Identifiers.IdentifierName(name.toString))))
    case untpd.Tuple(trees) =>
      PatternMatchings.TuplePattern(None, trees.map(extractPattern(_)))
    case _ => outOfSubsetError(pat, "This pattern is curently not supported")
  }


  def extractGuard(guard: Tree[Untyped])(implicit ctx: Context, dctx: DefContext): Option[Exprs.Expr] = guard match {
    case untpd.EmptyTree => None
    case a => Some(extractExpression(guard))
  }

  def extractCase(value: CaseDef[Untyped])(implicit ctx: Context, dctx: DefContext): PatternMatchings.MatchCase =
    PatternMatchings.MatchCase(extractPattern(value.pat), extractGuard(value.guard), extractBody(value.body))

  def extractExpression(expr: untpd.Tree)(implicit ctx: Context, dctx: DefContext): Exprs.Expr = (expr match {
    case Ident(name) =>
      val identifier = Identifiers.IdentifierName(name.toString.trim).setPos(expr.pos)
      Exprs.Variable(identifier)
//      if (dctx.isVariable(identifier))
//        Exprs.Variable(identifier).setPos(rhs.pos)
//      else
//        Exprs.Invocation(identifier, None, HSeq.fromSeq(Seq.empty[Exprs.Expr])).setPos(rhs.pos)
    case Apply(Ident(name), args) if name.toString == "Real" && args.length <= 2 && args.nonEmpty=>
      args.length match {
        case 1 => Exprs.FractionLiteral(extractBigIntValue(args.head), 1)
        case 2 => Exprs.FractionLiteral(extractBigIntValue(args.head), extractBigIntValue(args(1)))
      }
    case Apply(Ident(name), args) if name.toString == "Set" =>
      Exprs.SetConstruction(None, HSeq.fromSeq(args.map(extractExpression(_))))
    case Apply(Ident(name), args) if name.toString == "Bag" =>
      Exprs.BagConstruction(None, HSeq.fromSeq(args.map(extractPairs(_))))
    case Apply(TypeApply(Ident(name), targs), args) if name.toString == "Set" =>
      Exprs.SetConstruction(extractTypeArgs(targs),
        HSeq.fromSeq(args.map(extractExpression(_))))
    case Apply(TypeApply(Ident(name), targs), args) if name.toString == "Bag" =>
      Exprs.BagConstruction(extractTypeArgs(targs),
        HSeq.fromSeq(args.map(extractPairs(_))))

    case Literal(const) =>
      const.tag match {
        case Constants.LongTag =>
          Exprs.IntegerLiteral(const.longValue)
        case Constants.IntTag =>
          StainlessExprs.Int32Literal(const.intValue)
        case Constants.ShortTag =>
          StainlessExprs.Int16Literal(const.shortValue)
        case Constants.ByteTag =>
          StainlessExprs.Int8Literal(const.byteValue)
        case Constants.BooleanTag =>
          Exprs.BooleanLiteral(const.booleanValue)
        case Constants.StringTag =>
          Exprs.StringLiteral(const.stringValue)
        case Constants.CharTag =>
          Exprs.CharLiteral(const.charValue)
      }
    case untpd.Function(args, body) =>
      Exprs.Abstraction(Exprs.Lambda, extractBindings(args.asInstanceOf[Seq[untpd.ValDef]]), extractBody(body))
    case InfixOp(left, op, right) if op.name.toString == "->"=>
      Exprs.Tuple(HSeq.fromSeq(extractExpression(left) :: extractExpression(right) :: Nil))
    case InfixOp(left, op, right) =>
      makeInfixOp(op, left, right)
    case untpd.PrefixOp(op, body) =>
      makePrefixOp(op, body)
    case Apply(fun: untpd.Ident, args) =>
      Exprs.Invocation(Identifiers.IdentifierName(fun.name.toString), None, HSeq.fromSeq(args.map(extractExpression(_))))
    case If(cond, thenBranch, elseBranch) =>
      Exprs.If(extractExpression(cond), extractExpression(thenBranch), extractExpression(elseBranch))
    case untpd.Parens(expr) =>
      extractExpression(expr)
    case untpd.Tuple(trees) if trees.isEmpty=>
      Exprs.UnitLiteral()
    case untpd.Tuple(trees) =>
      Exprs.Tuple(HSeq.fromSeq(trees.map(extractExpression(_))))
    case ExTupleSelect(tree, int) =>
      Exprs.TupleSelection(extractExpression(tree), int)
    case Select(qualifier, name) =>
      Exprs.Selection(extractExpression(qualifier), Identifiers.IdentifierName(name.toString))
    case TypeApply(Select(qualifier, name), List(ident: untpd.Ident)) if name.toString == "isInstanceOf" =>
      Exprs.IsConstructor(extractExpression(qualifier), Identifiers.IdentifierName(ident.name.toString))
    case block: untpd.Block =>
      processBody(block.stats, block.expr)
    case Match(selector, cases) =>
      PatternMatchings.MatchExpression(extractExpression(selector), HSeq.fromSeq(cases.map(extractCase(_))))
    case untpd.EmptyTree =>
      Exprs.UnitLiteral()
    case _ =>
      outOfSubsetError(expr, "This tree is not supported at expression position")
  }).setPos(expr.pos)

  def processBody(stats: List[untpd.Tree], expr: untpd.Tree)(implicit ctx: Context, dctx: DefContext): Exprs.Expr = {
    def rec(stats: List[untpd.Tree]): Exprs.Expr = stats match {
      case (head:untpd.ValDef) :: Nil =>
        Exprs.Let(extractBinding(head), extractExpression(head.rhs),
          extractExpression(expr)).setPos(head.pos)
      case (head:untpd.ValDef) :: tail =>
        Exprs.Let(extractBinding(head), extractExpression(head.rhs),
          rec(tail)).setPos(head.pos)
      case (a @ Apply(_, _)) :: tail =>
        Exprs.Let(Bindings.InferredValDef(Identifiers.IdentifierName(FreshIdentifier.apply("binder").name)), extractExpression(a),
          rec(tail)
        ).setPos(stats.head.pos)
      case head :: tail => outOfSubsetError(head, "Currently not supported in body")
      case Nil => extractExpression(expr)
    }
    rec(stats)
  }

  def extractBody(body: untpd.Tree)(implicit ctx: Context, dctx: DefContext): Exprs.Expr = body match {
    case block: untpd.Block => processBody(block.stats, block.expr)
    case _ => extractExpression(body)
  }

  def extractBindings(constuctor: untpd.DefDef)(implicit ctx: Context): Bindings.BindingSeq = extractBindings(constuctor.vparamss.flatten)

  /**
    * Extracts static currently no classes, no modules, no classes and no imports
    * How to model modules in the current implementation
    *
    * @param stats list of trees
    * @return sequence of extracted sorts and functions
    */
  def extractStatic(stats: List[untpd.Tree])
                   (implicit inoxCtx: inox.Context, cache: SymbolsContext, ctx: Context):
  Seq[Either[ADTs.Sort, Function]] = {
    var result: Seq[Either[ADTs.Sort, Function]] = Seq()

    var constructorMaps = scala.collection.mutable.Map.empty[Identifiers.IdentifierName, List[ADTs.ConstructorValue]]
    var adtMap = scala.collection.mutable.Map.empty[Identifiers.IdentifierName, Identifiers.IdentifierSeq]

    var adts = Seq()

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
            case _: untpd.ValDef =>
            // ignore
            //            case vd@ValDef(_, _, _) if mods.flags.is(Flags.Module) =>
            //            //ignore
            //            case vd @ValDef(name, tpt, body: untpd.Function) if !mods.is(Flags.CaseAccessor) && !mods.is(Flags.ParamAccessor) &&
            //              !mods.is(Flags.Synthetic) && !mods.is(Flags.Mutable) =>
            //              result = result :+
            //                Right(Function(Identifiers.IdentifierName(vd.name.toString),
            //                  HSeq.fromSeq(Seq.empty[Identifiers.Identifier]), extractBindings(body.args.asInstanceOf[Seq[untpd.ValDef]]),
            //                  extractType(vd.tpt), extractBody(body.body)(ctx, DefContext())).setPos(stat.pos))
            //            case vd @ValDef(name, tpt, body) if !mods.is(Flags.CaseAccessor) && !mods.is(Flags.ParamAccessor) &&
            //              !mods.is(Flags.Synthetic) && !mods.is(Flags.Mutable) =>
            //              result = result :+
            //                Right(Function(Identifiers.IdentifierName(vd.name.toString),
            //                  HSeq.fromSeq(Seq.empty[Identifiers.Identifier]), HSeq.fromSeq(Seq.empty[Bindings.Binding]),
            //                  extractType(vd.tpt), extractBody(vd.rhs)(ctx, DefContext())).setPos(stat.pos))

            case module: untpd.ModuleDef if (mods.flags.is(Flags.ModuleClass) || mods.flags.is(Flags.Package))
              && !mods.flags.is(Flags.Synthetic) && !mods.flags.is(Flags.Case) =>
              result ++= extractObject(module)
            // case object for ADTS
            case untpd.ModuleDef(name, impl) if mods.is(Flags.Case) && !mods.is(Flags.Synthetic) &&
              impl.parents.size == 1 =>
              val sortIdent = Identifiers.IdentifierName(impl.parents.head.asInstanceOf[untpd.Ident].name.toString)
              val constructors = constructorMaps.getOrElseUpdate(
                sortIdent,
                List.empty)
              constructorMaps(sortIdent) = ADTs.ConstructorValue(Identifiers.IdentifierName(name.toString),
                extractBindings(impl.constr.vparamss.flatten)) :: constructors
            // abstract class as a root for ADT construction
            case TypeDef(name, tree: untpd.Template) if mods.is(Flags.Abstract) && !mods.is(Flags.Synthetic) =>
              val adtIdentifier = Identifiers.IdentifierName(name.toString())
              if (adtMap contains adtIdentifier)
                throw new Exception(s"ADT of the name $adtIdentifier is all ready defined")
              val params = extractTypeParams(tree.constr.tparams)
              adtMap(adtIdentifier) = params
            // case class as an ADT constructor
            case TypeDef(name, template: untpd.Template) if mods.is(Flags.CaseClass) && !mods.is(Flags.Synthetic)=>
              val sortIdent = Identifiers.IdentifierName(template.parents.head.asInstanceOf[untpd.Ident].name.toString)
              val constructors = constructorMaps.getOrElseUpdate(
                sortIdent,
                List.empty)
              constructorMaps(sortIdent) = ADTs.ConstructorValue(Identifiers.IdentifierName(name.toString),
                extractBindings(template.constr.vparamss.flatten)) :: constructors
            case f@ExFunctionDef(name, typeParams, valDefs, returnType, body) =>
              val bindings = extractBindings(valDefs)
              val parameterIdentifiers = bindings.elems.map {
                case Right(binding: Bindings.InferredValDef) => binding.identifier
                case Right(binding: Bindings.ExplicitValDef) => binding.identifier
                case _ => throw new Exception("Function extraction should not return anything other than a Right")
              }.toSet
              result = result :+
                Right(Function(Identifiers.IdentifierName(name.toString), extractTypeParams(typeParams),
                  extractBindings(valDefs), extractType(returnType),
                  extractBody(body)(ctx, DefContext(parameterIdentifiers))).setPos(stat.pos))
            case _ => outOfSubsetError(t, "Trying to extract a pair")
          }
    }

    val definedSorts = adtMap.toMap.keySet
    val usedSorts = constructorMaps.toMap.keySet

    if ((definedSorts diff usedSorts union (usedSorts diff definedSorts)).nonEmpty)
      throw new Exception("Some sorts are not well formed")

    for (adt <- adtMap) {
      val constructors: Seq[ADTs.Constructor] = constructorMaps.getOrElse(adt._1, Nil)
      if (constructors == Nil)
        throw new Exception(s"ADT ${adt._1.name} does not have any constructors")
      result = result :+Left(ADTs.Sort(adt._1, adt._2, HSeq.fromSeq(constructors)))
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

  object ExTupleSelect {
    private val Pattern = """_(\d{1,2})""".r

    def unapply(tree: untpd.Tree): Option[(untpd.Tree, Int)] = tree match {
      case Select(tuple, ExNamed(Pattern(n))) =>
        Some((tuple, n.toInt))
      case _ => None
    }
  }

  object ExNamed {
    def unapply(name: Name): Option[String] = Some(name.toString)
  }
}
