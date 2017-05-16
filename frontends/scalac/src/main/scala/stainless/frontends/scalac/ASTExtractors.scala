/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import scala.tools.nsc._

/** Contains extractors to pull-out interesting parts of the Scala ASTs. */
trait ASTExtractors {
  val global: Global

  import global._
  import global.definitions._

  def classFromName(str: String) = {
    rootMirror.getClassByName(newTypeName(str))
  }

  def objectFromName(str: String) = {
    rootMirror.getClassByName(newTermName(str))
  }

  def getAnnotations(sym: Symbol, ignoreOwner: Boolean = false): Map[String, Seq[Tree]] = {
    val actualSymbol = sym.accessedOrSelf
    (for {
      a <- actualSymbol.annotations ++ (if (!ignoreOwner) actualSymbol.owner.annotations else Set.empty)
      name = a.atp.safeToString.replaceAll("\\.package\\.", ".")
    } yield {
      if (name startsWith "stainless.annotation.") {
        val shortName = name drop "stainless.annotation.".length
        Some(shortName, a.args)
      } else if (name == "inline") {
        Some(name, a.args)
      } else {
        None
      }
    }).flatten.toMap
  }

  protected lazy val scalaMapSym = classFromName("scala.collection.immutable.Map")
  protected lazy val scalaSetSym = classFromName("scala.collection.immutable.Set")
  protected lazy val setSym      = classFromName("stainless.lang.Set")
  protected lazy val mapSym      = classFromName("stainless.lang.Map")
  protected lazy val bagSym      = classFromName("stainless.lang.Bag")
  protected lazy val realSym     = classFromName("stainless.lang.Real")

  protected lazy val optionSymbol = classFromName("stainless.lang.Option")
  protected lazy val someSymbol   = classFromName("stainless.lang.Some")
  protected lazy val noneSymbol   = classFromName("stainless.lang.None")

  protected lazy val listSymbol = classFromName("stainless.collection.List")
  protected lazy val consSymbol = classFromName("stainless.collection.Cons")
  protected lazy val nilSymbol  = classFromName("stainless.collection.Nil")

  protected lazy val arraySym           = classFromName("scala.Array")
  protected lazy val someClassSym       = classFromName("scala.Some")
  protected lazy val byNameSym          = classFromName("scala.<byname>")
  protected lazy val bigIntSym          = classFromName("scala.math.BigInt")
  protected lazy val stringSym          = classFromName("java.lang.String")

  protected def functionTraitSym(i:Int) = {
    require(0 <= i && i <= 22)
    classFromName("scala.Function" + i)
  }

  def isTuple(sym: Symbol, size: Int): Boolean = (size > 0) && (sym == classFromName(s"scala.Tuple$size"))

  def isBigIntSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) == bigIntSym

  def isStringSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) match { case `stringSym` => true case _ => false }

  def isByNameSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) == byNameSym

  // Resolve type aliases
  def getResolvedTypeSym(sym: Symbol): Symbol = {
    if (sym.isAliasType) {
      getResolvedTypeSym(sym.tpe.resultType.typeSymbol)
    } else {
      sym
    }
  }

  def isSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == setSym
  }

  def isBagSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == bagSym
  }

  def isRealSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == realSym
  }

  def isScalaSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaSetSym
  }

  def isMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == mapSym
  }

  def isScalaMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaMapSym
  }

  def isFunction(sym: Symbol, i: Int) : Boolean =
    0 <= i && i <= 22 && sym == functionTraitSym(i)

  def isArrayClassSym(sym: Symbol): Boolean = sym == arraySym

  private val bvtypes = Set(ByteTpe, ShortTpe, IntTpe, LongTpe)

  def hasBVType(t: Tree) = bvtypes contains t.tpe.widen

  def hasNumericType(t: Tree): Boolean = hasBigIntType(t) || hasBVType(t) || hasRealType(t)

  def hasBigIntType(t: Tree) = isBigIntSym(t.tpe.typeSymbol)

  def hasStringType(t: Tree) = isStringSym(t.tpe.typeSymbol)

  def hasRealType(t: Tree) = isRealSym(t.tpe.typeSymbol)

  def hasBooleanType(t: Tree) = t.tpe.widen =:= BooleanClass.tpe

  /** A set of helpers for extracting trees.*/
  object ExtractorHelpers {
    /** Extracts the identifier as `"Ident(name)"` (who needs this?!) */
    object ExIdNamed {
      def unapply(id: Ident): Option[String] = Some(id.toString)
    }

    /** Extracts the tree and its type (who needs this?!) */
    object ExHasType {
      def unapply(tr: Tree): Option[(Tree, Symbol)] = Some((tr, tr.tpe.typeSymbol))
    }

    /** Extracts the string representation of a name of something having the `Name` trait */
    object ExNamed {
      def unapply(name: Name): Option[String] = Some(name.toString)
    }

    /** Returns the full dot-separated names of the symbol as a list of strings */
    object ExSymbol {
      def unapplySeq(t: Tree): Option[Seq[String]] = {
        if (t.symbol == null) None
        else Some(t.symbol.fullName.toString.split('.').toSeq)
      }
    }

    /** Matches nested `Select(Select(...Select(a, b) ...y) , z)` and returns the list `a,b, ... y,z` */
    object ExSelected {
      def unapplySeq(select: Select): Option[Seq[String]] = select match {
        case Select(This(scalaName), name) =>
          Some(Seq(scalaName.toString, name.toString))

        case Select(from: Select, name) =>
          unapplySeq(from).map(prefix => prefix :+ name.toString)

        case Select(from: Ident, name) =>
          Some(Seq(from.toString, name.toString))

        case _ =>
          None
      }
    }
  }

  object StructuralExtractors {
    import ExtractorHelpers._

    /** Extracts the 'ensuring' contract from an expression. */
    object ExEnsuredExpression {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(Apply(TypeApply(ExSelected("scala", "Predef", "Ensuring"), _ :: Nil), body :: Nil), ExNamed("ensuring")), contract :: Nil)
          => Some((body, contract))
        case Apply(Select(Apply(TypeApply(ExSelected("stainless", "lang", "StaticChecks", "any2Ensuring"), _ :: Nil), body :: Nil), ExNamed("ensuring")), contract :: Nil)
          => Some((body, contract))
        case _ => None
      }
    }

    /** Matches the `holds` expression at the end of any boolean expression, and returns the boolean expression.*/
    object ExHoldsExpression {
      def unapply(tree: Select) : Option[Tree] = tree match {
        case Select(
          Apply(ExSelected("stainless", "lang", "package", "BooleanDecorations"), realExpr :: Nil),
          ExNamed("holds")
        ) => Some(realExpr)
        case _ => None
       }
    }
    
    /** Matches the `holds` expression at the end of any boolean expression with a proof as argument, and returns both of themn.*/
    object ExHoldsWithProofExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(Apply(ExSelected("stainless", "lang", "package", "BooleanDecorations"), body :: Nil), ExNamed("holds")), proof :: Nil) =>
          Some((body, proof))
        case _ => None
       }
    }
    
    /** Matches the `because` method at the end of any boolean expression, and return the assertion and the cause. If no "because" method, still returns the expression */
    object ExMaybeBecauseExpressionWrapper {
      def unapply(tree: Tree) : Some[Tree] = tree match {
        case Apply(ExSelected("stainless", "lang", "package", "because"), body :: Nil) =>
          unapply(body)
        case body => Some(body)
       }
    }
    
    /** Matches the `because` method at the end of any boolean expression, and return the assertion and the cause.*/
    object ExBecauseExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(Apply(ExSelected("stainless", "proof", "package", "boolean2ProofOps"), body :: Nil), ExNamed("because")), proof :: Nil) =>
          Some((body, proof))
        case _ => None
       }
    }
    
    /** Matches the `bigLength` expression at the end of any string expression, and returns the expression.*/
    object ExBigLengthExpression {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case Apply(Select(
          Apply(ExSelected("stainless", "lang", "package", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigLength")), Nil)
          => Some(stringExpr)
        case _ => None
       }
    }
    
    /** Matches the `bigSubstring` method at the end of any string expression, and returns the expression and the start index expression.*/
    object ExBigSubstringExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(
          Apply(ExSelected("stainless", "lang", "package", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigSubstring")), startExpr :: Nil)
           => Some(stringExpr, startExpr)
        case _ => None
       }
    }
    
    /** Matches the `bigSubstring` expression at the end of any string expression, and returns the expression, the start and end index expressions.*/
    object ExBigSubstring2Expression {
      def unapply(tree: Apply) : Option[(Tree, Tree, Tree)] = tree match {
        case Apply(Select(
          Apply(ExSelected("stainless", "lang", "package", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigSubstring")), startExpr :: endExpr :: Nil)
           => Some(stringExpr, startExpr, endExpr)
        case _ => None
       }
    }

    /** Matches an implication `lhs ==> rhs` and returns (lhs, rhs)*/
    object ExImplies {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case
          Apply(
            Select(
              Apply(
                ExSymbol("stainless", "lang", "BooleanDecorations"),
                lhs :: Nil
              ),
              ExNamed("$eq$eq$greater")
            ),
            rhs :: Nil
          ) => Some((lhs, rhs))
        case _ => None
      }
    }

    /** Extracts the 'require' contract from an expression (only if it's the
     * first call in the block). */
    object ExRequiredExpression {
      def unapply(tree: Apply): Option[Tree] = tree match {
        case Apply(ExSelected("scala", "Predef", "require"), contractBody :: Nil) =>
         Some(contractBody)
        case _ => None
      }
    }

    /** Extracts the 'decreases' contract for an expression (should be right after 'require') */
    object ExDecreasesExpression {
      def unapply(tree: Apply): Option[Seq[Tree]] = tree match {
        case Apply(ExSelected("stainless", "lang", "package", "decreases"), args) =>
          Some(args)
        case _ => None
      }
    }

    /** Extracts the implicit wrapper that provides support for higher-order contracts.
      *
      * @see [[ExRequiresExpression]], [[ExEnsuresExpression]], [[ExPreExpression]] */
    object ExFunctionSpecs {
      def unapply(tree: Tree): Option[Tree] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "FunctionSpecs0"), Seq(_)), Seq(f)) => Some(f)
        case Apply(TypeApply(ExSymbol("stainless", "lang", "FunctionSpecs1"), Seq(_, _)), Seq(f)) => Some(f)
        case Apply(TypeApply(ExSymbol("stainless", "lang", "FunctionSpecs2"), Seq(_, _, _)), Seq(f)) => Some(f)
        case Apply(TypeApply(ExSymbol("stainless", "lang", "FunctionSpecs3"), Seq(_, _, _, _)), Seq(f)) => Some(f)
        case Apply(TypeApply(ExSymbol("stainless", "lang", "FunctionSpecs4"), Seq(_, _, _, _, _)), Seq(f)) => Some(f)

        case Select(ExSymbol("stainless", "lang", "FunctionSpecs0"), ExNamed("f")) => Some(tree)
        case Select(ExSymbol("stainless", "lang", "FunctionSpecs1"), ExNamed("f")) => Some(tree)
        case Select(ExSymbol("stainless", "lang", "FunctionSpecs2"), ExNamed("f")) => Some(tree)
        case Select(ExSymbol("stainless", "lang", "FunctionSpecs3"), ExNamed("f")) => Some(tree)
        case Select(ExSymbol("stainless", "lang", "FunctionSpecs4"), ExNamed("f")) => Some(tree)

        case _ => None
      }
    }

    /** Extracts the first-class contract 'pre'. */
    object ExPreExpression {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(ExFunctionSpecs(f), ExNamed("pre")) => Some(f)
        case _ => None
      }
    }

    /** Matches the `A computes B` expression at the end of any expression A, and returns (A, B). */
    object ExComputesExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(
          Apply(TypeApply(ExSelected("stainless", "lang", "package", "SpecsDecorations"), List(_)), realExpr :: Nil),
          ExNamed("computes")), expected::Nil)
         => Some((realExpr, expected))
        case _ => None
       }
    }

    /** Matches the `O ask I` expression at the end of any expression O, and returns (I, O).*/
    object ExAskExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(TypeApply(Select(
          Apply(TypeApply(ExSelected("stainless", "lang", "package", "SpecsDecorations"), List(_)), output :: Nil),
          ExNamed("ask")), List(_)), input::Nil)
         => Some((input, output))
        case _ => None
       }
    }

    object ExByExampleExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(TypeApply(ExSelected("stainless", "lang", "package", "byExample"), List(_, _)), input :: res_output :: Nil)
         => Some((input, res_output))
        case _ => None
       }
    }

    /** Extracts the `(input, output) passes { case In => Out ...}` and returns (input, output, list of case classes) */
    object ExPasses {
      def unapply(tree : Apply) : Option[(Tree, Tree, List[CaseDef])] = tree match {
        case  Apply(
                Select(
                  Apply(
                    TypeApply(
                      ExSelected("stainless", "lang", "package", "Passes"),
                      List(_, _)
                    ),
                    List(ExpressionExtractors.ExTuple(_, Seq(in,out)))
                  ),
                  ExNamed("passes")
                ),
                List(Function(
                  List(ValDef(_, _, _, EmptyTree)),
                  ExpressionExtractors.ExPatternMatching(_,tests)
                ))
              )
          => Some((in, out, tests))
        case _ => None
      }
    }

    /** Returns a string literal from a constant string literal. */
    object ExStringLiteral {
      def unapply(tree: Tree): Option[String] = tree  match {
        case Literal(c @ Constant(i)) if c.tpe == StringClass.tpe =>
          Some(c.stringValue)
        case _ =>
          None
      }
    }

    /** Returns the arguments of an unapply pattern */
    object ExUnapplyPattern {
      def unapply(tree: Tree): Option[(Tree, Seq[Tree])] = tree match {
        case UnApply(Apply(s, _), args) =>
          Some((s, args))
        case _ => None
      }
    }

    /** Returns the argument of a bigint literal, either from scala or stainless */
    object ExBigIntLiteral {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(ExSelected("scala", "package", "BigInt", "apply"), n :: Nil) =>
          Some(n)
        case Apply(ExSelected("stainless", "lang", "package", "BigInt", "apply"), n :: Nil) =>
          Some(n)
        case _ =>
          None
      }
    }

    /** Returns the two components (n, d) of a real n/d literal */
    object ExRealLiteral {
      def unapply(tree: Tree): Option[(Tree, Tree)] = tree  match {
        case Apply(ExSelected("stainless", "lang", "Real", "apply"), n :: d :: Nil) =>
          Some((n, d))
        case _ =>
          None
      }
    }

    /** Matches Real(x) when n is an integer and returns x */
    object ExRealIntLiteral {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(ExSelected("stainless", "lang", "Real", "apply"), n :: Nil) =>
          Some(n)
        case _ =>
          None
      }
    }

    /** Matches the construct int2bigInt(a) and returns a */
    object ExIntToBigInt {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(ExSelected("math", "BigInt", "int2bigInt"), tree :: Nil) => Some(tree)
        case _ => None
      }
    }

    /** Matches the construct List[tpe](a, b, ...) and returns tpe and arguments */
    object ExListLiteral {
      def unapply(tree: Apply): Option[(Tree, List[Tree])] = tree  match {
        case Apply(
              TypeApply(ExSelected("stainless", "collection", "List", "apply"), tpe :: Nil),
              args) =>
          Some((tpe, args))
        case _ =>
          None
      }
    }

    /** Extracts the 'assert' contract from an expression (only if it's the
      * first call in the block). */
    object ExAssertExpression {
      def unapply(tree: Apply): Option[(Tree, Option[String])] = tree match {
        case Apply(ExSymbol("scala", "Predef", "assert"), contractBody :: Nil) =>
          Some((contractBody, None))
        case Apply(ExSymbol("scala", "Predef", "assert"), contractBody :: (error: Literal) :: Nil) =>
          Some((contractBody, Some(error.value.stringValue)))
        case _ =>
          None
      }
    }

    /** Matches an object with no type parameters, and regardless of its
      * visibility. Does not match on case objects or the automatically generated companion
      * objects of case classes (or any synthetic class). */
    object ExObjectDef {
      def unapply(cd: ClassDef): Option[(String,Template)] = cd match {
        case ClassDef(_, name, tparams, impl) if
          (cd.symbol.isModuleClass || cd.symbol.hasPackageFlag) &&
          tparams.isEmpty &&
          !cd.symbol.isSynthetic &&
          !cd.symbol.isCaseClass
        => {
          Some((name.toString, impl))
        }
        case _ => None
      }
    }

    object ExCaseObject {
      def unapply(s: Select): Option[Symbol] = {
        if (s.tpe.typeSymbol.isModuleClass) {
          Some(s.tpe.typeSymbol)
        } else {
          None
        }
      }
    }

    object ExCompanionObjectSynthetic {
      def unapply(cd : ClassDef) : Option[(String, Symbol, Template)] = {
        val sym = cd.symbol
        cd match {
         case ClassDef(_, name, tparams, impl) if sym.isModule && sym.isSynthetic => //FIXME flags?
           Some((name.toString, sym, impl))
         case _ => None
        }

      }
    }

    object ExCaseClassSyntheticJunk {
      def unapply(cd: Tree): Boolean = cd match {
        case ClassDef(_, _, _, _) if cd.symbol.isSynthetic => true
        case DefDef(_, _, _, _, _, _) if cd.symbol.isSynthetic && (cd.symbol.isCase || cd.symbol.isPrivate) => true
        case _ => false
      }
    }

    object ExConstructorDef {
      def unapply(dd: DefDef): Boolean = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if name == nme.CONSTRUCTOR && tparams.isEmpty => true
        case _ => false
      }
    }

    object ExMainFunctionDef {
      def unapply(dd: DefDef): Boolean = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if name.toString == "main" && tparams.isEmpty && vparamss.size == 1 && vparamss.head.size == 1 => {
          true
        }
        case _ => false
      }
    }

    object ExFunctionDef {
      /** Matches a function with a single list of arguments, and regardless of its visibility. */
      def unapply(dd: DefDef): Option[(Symbol, Seq[Symbol], Seq[ValDef], Type, Tree)] = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if name != nme.CONSTRUCTOR && !dd.symbol.isAccessor =>
          if ((
            // extract implicit class construction functions
            dd.symbol.isSynthetic &&
            dd.symbol.isImplicit &&
            dd.symbol.isMethod &&
            !(getAnnotations(tpt.symbol) contains "ignore")
          ) || (
            !dd.symbol.isSynthetic
          )) {
            Some((dd.symbol, tparams.map(_.symbol), vparamss.flatten, tpt.tpe, rhs))
          } else {
            None
          }
        case _ => None
      }
    }

    object ExLazyAccessorFunction {
      def unapply(dd: DefDef): Option[(Symbol, Type, Tree)] = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(
          vparamss.size <= 1 && name != nme.CONSTRUCTOR &&
          !dd.symbol.isSynthetic && dd.symbol.isAccessor && dd.symbol.isLazy
        ) =>
          Some((dd.symbol, tpt.tpe, rhs))
        case _ => None
      }
    }

    object ExMutatorAccessorFunction {
      def unapply(dd: DefDef): Option[(Symbol, Seq[Symbol], Seq[ValDef], Type, Tree)] = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(
          vparamss.size <= 1 && name != nme.CONSTRUCTOR &&
          !dd.symbol.isSynthetic && dd.symbol.isAccessor && name.endsWith("_$eq")
        ) =>
          Some((dd.symbol, tparams.map(_.symbol), vparamss.flatten, tpt.tpe, rhs))
        case _ => None
      }
    }

    object ExMutableFieldDef {

      /** Matches a definition of a strict var field inside a class constructor */
      def unapply(vd: SymTree) : Option[(Symbol, Type, Tree)] = {
        val sym = vd.symbol
        vd match {
          // Implemented fields
          case ValDef(mods, name, tpt, rhs) if (
            !sym.isCaseAccessor && !sym.isParamAccessor &&
            !sym.isLazy && !sym.isSynthetic && !sym.isAccessor && sym.isVar
          ) =>
            println("matched a var accessor field: sym is: " + sym)
            println("getterIn is: " + sym.getterIn(sym.owner))
            // Since scalac uses the accessor symbol all over the place, we pass that instead:
            Some( (sym.getterIn(sym.owner),tpt.tpe,rhs) )
          case _ => None
        }
      }
    }

    object ExFieldDef {
      /** Matches a definition of a strict field inside a class constructor */
      def unapply(vd: SymTree) : Option[(Symbol, Type, Tree)] = {
        val sym = vd.symbol
        vd match {
          // Implemented fields
          case ValDef(mods, name, tpt, rhs) if (
            !sym.isCaseAccessor && !sym.isParamAccessor &&
            !sym.isLazy && !sym.isSynthetic && !sym.isAccessor && !sym.isVar
          ) =>
            // Since scalac uses the accessor symbol all over the place, we pass that instead:
            Some( (sym.getterIn(sym.owner),tpt.tpe,rhs) )
          // Unimplemented fields
          case df @ DefDef(_, name, _, _, tpt, _) if (
            sym.isStable && sym.isAccessor && sym.name != nme.CONSTRUCTOR &&
            sym.accessed == NoSymbol // This is to exclude fields with implementation
          ) =>
            Some( (sym, tpt.tpe, EmptyTree))
          case _ => None
        }
      }
    }

    object ExLazyFieldDef {
      /** Matches lazy field definitions.
       *  WARNING: Do NOT use this as extractor for lazy fields,
       *  as it does not contain the body of the lazy definition.
       *  It is here just to signify a Definition acceptable by Leon
       */
      def unapply(vd: ValDef) : Boolean = {
        val sym = vd.symbol
        vd match {
          case ValDef(mods, name, tpt, rhs) if (
            sym.isLazy && !sym.isCaseAccessor && !sym.isParamAccessor &&
            !sym.isSynthetic && !sym.isAccessor
          ) =>
            // Since scalac uses the accessor symbol all over the place, we pass that instead:
            true
          case _ => false
        }
      }
    }

    object ExFieldAccessorFunction{
      /** Matches the accessor function of a field
       *  WARNING: This is not meant to be used for any useful purpose,
       *  other than to satisfy Definition acceptable by Leon
       */
      def unapply(dd: DefDef): Boolean = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(
          vparamss.size <= 1 && name != nme.CONSTRUCTOR &&
          dd.symbol.isAccessor && !dd.symbol.isLazy
        ) =>
          true
        case _ => false
      }
    }

    object ExDefaultValueFunction{
      /** Matches a function that defines the default value of a parameter */
      def unapply(dd: DefDef): Option[(Symbol, Seq[Symbol], Seq[ValDef], Type, String, Int, Tree)] = {
        val sym = dd.symbol
        dd match {
          case DefDef(_, name, tparams, vparamss, tpt, rhs) if(
            vparamss.size <= 1 && name != nme.CONSTRUCTOR && sym.isSynthetic
          ) =>

            // Split the name into pieces, to find owner of the parameter + param.index
            // Form has to be <owner name>$default$<param index>
            val symPieces = sym.name.toString.reverse.split("\\$", 3).reverseMap(_.reverse)

            try {
              if (symPieces(1) != "default" || symPieces(0) == "copy") throw new IllegalArgumentException("")
              val ownerString = symPieces(0)
              val index = symPieces(2).toInt - 1
              Some((sym, tparams.map(_.symbol), vparamss.headOption.getOrElse(Nil), tpt.tpe, ownerString, index, rhs))
            } catch {
              case _ : NumberFormatException | _ : IllegalArgumentException | _ : ArrayIndexOutOfBoundsException =>
                None
            }

          case _ => None
        }
      }
    }
  }

  object ExpressionExtractors {
    import ExtractorHelpers._

    object ExEpsilonExpression {
      def unapply(tree: Apply) : Option[(Tree, Symbol, Tree)] = tree match {
        case Apply(
              TypeApply(ExSymbol("stainless", "lang", "xlang", "epsilon"), typeTree :: Nil),
              Function((vd @ ValDef(_, _, _, EmptyTree)) :: Nil, predicateBody) :: Nil) =>
            Some((typeTree, vd.symbol, predicateBody))
        case _ => None
      }
    }

    object ExErrorExpression {
      def unapply(tree: Apply) : Option[(String, Tree)] = tree match {
        case a @ Apply(TypeApply(ExSymbol("stainless", "lang", "error"), List(tpe)), List(lit : Literal)) =>
          Some((lit.value.stringValue, tpe))
        case _ =>
          None
      }
    }

    object ExOldExpression {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case a @ Apply(TypeApply(ExSymbol("stainless", "lang", "old"), List(tpe)), List(arg)) =>
          Some(arg)
        case _ =>
          None
      }
    }

    object ExHoleExpression {
      def unapply(tree: Tree) : Option[(Tree, List[Tree])] = tree match {
        case a @ Apply(TypeApply(s @ ExSymbol("stainless", "lang", "synthesis", "$qmark"), List(tpt)), args1)  =>
            Some((tpt, args1))
        case TypeApply(s @ ExSymbol("stainless", "lang", "synthesis", "$qmark$qmark$qmark"), List(tpt)) =>
            Some((tpt, Nil))
        case _ => None
      }
    }

    object ExChooseExpression {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case a @ Apply(
              TypeApply(s @ ExSymbol("stainless", "lang", "choose"), types),
              predicate :: Nil) =>
            Some(predicate)
        case _ => None
      }
    }

    object ExWithOracleExpression {
      def unapply(tree: Apply) : Option[(List[(Tree, Symbol)], Tree)] = tree match {
        case a @ Apply(
              TypeApply(s @ ExSymbol("stainless", "lang", "synthesis", "withOracle"), types),
              Function(vds, body) :: Nil) =>
            Some((types zip vds.map(_.symbol), body))
        case _ => None
      }
    }

    object ExLambdaExpression {
      def unapply(tree: Function) : Option[(Seq[ValDef], Tree)] = tree match {
        case Function(vds, body) => Some((vds, body))
        case _ => None
      }
    }

    object ExForallExpression {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case a @ Apply(
            TypeApply(s @ ExSymbol("stainless", "lang", "forall"), _),
            predicate :: Nil) =>
          Some(predicate)
        case _ => None
      }
    }

    object ExArrayUpdated {
      def unapply(tree: Apply): Option[(Tree,Tree,Tree)] = tree match {
        case Apply(
              Apply(TypeApply(Select(Apply(ExSymbol("scala", "Predef", s), Seq(lhs)), n), _), Seq(index, value)),
              List(Apply(_, _))) if (s.toString contains "Array") && (n.toString == "updated") => Some((lhs, index, value))
        case _ => None
      }
    }

    object ExValDef {
      /** Extracts val's in the head of blocks. */
      def unapply(tree: ValDef): Option[(Symbol,Tree,Tree)] = tree match {
        case vd @ ValDef(mods, _, tpt, rhs) if !mods.isMutable => Some((vd.symbol, tpt, rhs))
        case _ => None
      }
    }
    object ExVarDef {
      /** Extracts var's in the head of blocks. */
      def unapply(tree: ValDef): Option[(Symbol,Tree,Tree)] = tree match {
        case vd @ ValDef(mods, _, tpt, rhs) if mods.isMutable => Some((vd.symbol, tpt, rhs))
        case _ => None
      }
    }

    object ExAssign {
      def unapply(tree: Assign): Option[(Symbol,Tree)] = tree match {
        case Assign(id@Ident(_), rhs) => Some((id.symbol, rhs))
        //case Assign(sym@Select(This(_), v), rhs) => Some((sym.symbol, rhs))
        case _ => None
      }
    }

    object ExWhile {
      def unapply(tree: LabelDef): Option[(Tree,Tree)] = tree match {
        case (label@LabelDef(
                _, _, If(cond, Block(body, jump@Apply(_, _)), unit@ExUnitLiteral())))
              if label.symbol == jump.symbol && unit.symbol == null => Some((cond, Block(body, unit)))
        case _ => None
      }
    }

    object ExWhileWithInvariant {
      def unapply(tree: Apply): Option[(Tree, Tree, Tree)] = tree match {
        case Apply(
          Select(
            Apply(while2invariant, List(ExWhile(cond, body))),
            invariantSym),
          List(invariant)) if invariantSym.toString == "invariant" => Some((cond, body, invariant))
        case _ => None
      }
    }

    object ExArrayLiteral {
      def unapply(tree: Apply): Option[(Type, Seq[Tree])] = tree match {
        case Apply(ExSelected("scala", "Array", "apply"), args) =>
          tree.tpe match {
            case TypeRef(_, _, List(t1)) =>
              Some((t1, args))
            case _ =>
              None
          }
        case Apply(Apply(TypeApply(ExSelected("scala", "Array", "apply"), List(tpt)), args), ctags) =>
          Some((tpt.tpe, args))

        case _ =>
          None
      }
    }

    object ExTuple {
      def unapply(tree: Apply): Option[(Seq[Type], Seq[Tree])] = tree match {
        case Apply(Select(New(tupleType), _), args) if isTuple(tupleType.symbol, args.size) =>
          tupleType.tpe match {
            case TypeRef(_, _, tps) => Some(tps, args)
            case _ => None
          }

        // Match e1 -> e2
        case Apply(TypeApply(Select(Apply(TypeApply(ExSelected("scala", "Predef", "ArrowAssoc"), List(tpeFrom)), List(from)), ExNamed("$minus$greater")), List(tpeTo)), List(to)) =>
          Some((Seq(tpeFrom.tpe, tpeTo.tpe), Seq(from, to)))

        case _ => None
      }
    }

    object ExLocally {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case Apply(TypeApply(ExSelected("scala", "Predef", "locally"), _), List(body)) =>
          Some(body)

        case _ =>
          None
      }
    }

    object ExTupleExtract {
      def unapply(tree: Select) : Option[(Tree,Int)] = tree match {
        case Select(lhs, n) => {
          val methodName = n.toString
          if(methodName.head == '_') {
            val indexString = methodName.tail
            try {
              val index = indexString.toInt
              if(index > 0) {
                Some((lhs, index))
              } else None
            } catch {
              case t: Throwable =>
                None
            }
          } else None
        }
        case _ => None
      }
    }

    object ExIfThenElse {
      def unapply(tree: If): Option[(Tree,Tree,Tree)] = tree match {
        case If(t1,t2,t3) => Some((t1,t2,t3))
        case _ => None
      }
    }

    object ExBooleanLiteral {
      def unapply(tree: Literal): Option[Boolean] = tree match {
        case Literal(Constant(true)) => Some(true)
        case Literal(Constant(false)) => Some(false)
        case _ => None
      }
    }

    object ExCharLiteral {
      def unapply(tree: Literal): Option[Char] = tree match {
        case Literal(c @ Constant(i)) if c.tpe == CharTpe => Some(c.charValue)
        case _ => None
      }
    }

    object ExInt8Literal {
      def unapply(tree: Literal): Option[Byte] = tree match {
        case Literal(c @ Constant(i)) if c.tpe == ByteTpe => Some(c.byteValue)
        case _ => None
      }
    }

    object ExInt16Literal {
      def unapply(tree: Literal): Option[Short] = tree match {
        case Literal(c @ Constant(i)) if c.tpe == ShortTpe => Some(c.shortValue)
        case _ => None
      }
    }

    object ExInt32Literal {
      def unapply(tree: Literal): Option[Int] = tree match {
        case Literal(c @ Constant(i)) if c.tpe == IntTpe => Some(c.intValue)
        case _ => None
      }
    }

    object ExInt64Literal {
      def unapply(tree: Literal): Option[Long] = tree match {
        case Literal(c @ Constant(i)) if c.tpe == LongTpe => Some(c.longValue)
        case _ => None
      }
    }

    object ExUnitLiteral {
      def unapply(tree: Literal): Boolean = tree match {
        case Literal(c @ Constant(_)) if c.tpe == UnitTpe => true
        case _ => false
      }
    }

    object ExClassConstruction {
      def unapply(tree: Apply): Option[(Tree,Seq[Tree])] = tree match {
        case Apply(s @ Select(New(tpt), n), args) if n == nme.CONSTRUCTOR =>
          Some((tpt, args))
        case _ => None
      }
    }

    object ExIdentifier {
      def unapply(tree: Ident): Option[(Symbol,Tree)] = tree match {
        case i: Ident => Some((i.symbol, i))
        case _ => None
      }
    }

    object ExTyped {
      def unapply(tree : Typed): Option[(Tree,Tree)] = tree match {
        case Typed(e,t) => Some((e,t))
        case _ => None
      }
    }

    object ExIntIdentifier {
      def unapply(tree: Ident): Option[String] = tree match {
        case i: Ident if i.symbol.tpe == IntClass.tpe => Some(i.symbol.name.toString)
        case _ => None
      }
    }

    object ExAnd {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(s @ Select(lhs, _), List(rhs)) if s.symbol == Boolean_and =>
          Some((lhs,rhs))
        case _ => None
      }
    }

    object ExOr {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(s @ Select(lhs, _), List(rhs)) if s.symbol == Boolean_or =>
          Some((lhs,rhs))
        case _ => None
      }
    }

    object ExNot {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if n == nme.UNARY_! && hasBooleanType(t) => Some(t)
        case _ => None
      }
    }

    object ExEquals {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if n == nme.EQ => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExNotEquals {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if n == nme.NE => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExUMinus {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if n == nme.UNARY_- && hasNumericType(t) => Some(t)
        case _ => None
      }
    }

    object ExBVNot {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if n == nme.UNARY_~ && hasBVType(t) => Some(t)
        case _ => None
      }
    }

    object ExPatternMatching {
      def unapply(tree: Match): Option[(Tree,List[CaseDef])] =
        if(tree != null) Some((tree.selector, tree.cases)) else None
    }

    object ExBigIntPattern {
      def unapply(tree: UnApply): Option[Tree] = tree match {
        case ua @ UnApply(Apply(ExSelected("stainless", "lang", "package", "BigInt", "unapply"), _), List(l)) =>
          Some(l)
        case _ =>
          None
      }
    }

    object ExAsInstanceOf {
      def unapply(tree: TypeApply) : Option[(Tree, Tree)] = tree match {
        case TypeApply(Select(t, isInstanceOfName), typeTree :: Nil) if isInstanceOfName.toString == "asInstanceOf" => Some((t, typeTree))
        case _ => None
      }
    }

    object ExIsInstanceOf {
      def unapply(tree: TypeApply) : Option[(Tree, Tree)] = tree match {
        case TypeApply(Select(t, isInstanceOfName), typeTree :: Nil) if isInstanceOfName.toString == "isInstanceOf" => Some((t, typeTree))
        case _ => None
      }
    }

    object ExLiteralMap {
      def unapply(tree: Apply): Option[(Tree, Tree, Seq[Tree])] = tree match {
        case Apply(TypeApply(ExSelected("scala", "Predef", "Map", "apply"), fromTypeTree :: toTypeTree :: Nil), args) =>
          Some((fromTypeTree, toTypeTree, args))
        case _ =>
          None
      }
    }
    object ExEmptyMap {
      def unapply(tree: TypeApply): Option[(Tree, Tree)] = tree match {
        case TypeApply(ExSelected("scala", "collection", "immutable", "Map", "empty"), fromTypeTree :: toTypeTree :: Nil) =>
          Some((fromTypeTree, toTypeTree))
        case TypeApply(ExSelected("scala", "Predef", "Map", "empty"), fromTypeTree :: toTypeTree :: Nil) =>
          Some((fromTypeTree, toTypeTree))
        case _ =>
          None
      }
    }

    object ExFiniteSet {
      def unapply(tree: Apply): Option[(Tree,List[Tree])] = tree match {
        case Apply(TypeApply(ExSelected("Set", "apply"), Seq(tpt)), args) =>
          Some(tpt, args)
        case Apply(TypeApply(ExSelected("stainless", "lang", "Set", "apply"), Seq(tpt)), args) =>
          Some(tpt, args)
        case _ => None
      }
    }

    object ExFiniteBag {
      def unapply(tree: Apply): Option[(Tree, List[Tree])] = tree match {
        case Apply(TypeApply(ExSelected("Bag", "apply"), Seq(tpt)), args) =>
          Some(tpt, args)
        case Apply(TypeApply(ExSelected("stainless", "lang", "Bag", "apply"), Seq(tpt)), args) =>
          Some(tpt, args)
        case _ => None
      }
    }

    object ExFiniteMap {
      def unapply(tree: Apply): Option[(Tree, Tree, List[Tree])] = tree match {
        case Apply(TypeApply(ExSelected("Map", "apply"), Seq(tptFrom, tptTo)), args) =>
          Some((tptFrom, tptTo, args))
        case Apply(TypeApply(ExSelected("stainless", "lang", "Map", "apply"), Seq(tptFrom, tptTo)), args) =>
          Some((tptFrom, tptTo, args))
        case _ => None
      }
    }

    object ExParameterLessCall {
      def unapply(tree: Tree): Option[(Tree, Symbol, Seq[Tree])] = tree match {
        case s @ Select(t, _) =>
          Some((t, s.symbol, Nil))

        case TypeApply(s @ Select(t, _), tps) =>
          Some((t, s.symbol, tps))

        case TypeApply(i: Ident, tps) =>
          Some((i, i.symbol, tps))

        case _ =>
          None
      }
    }

    object ExCall {
      def unapply(tree: Tree): Option[(Option[Tree], Symbol, Seq[Tree], Seq[Tree])] = {
        val res = tree match {
          // a.foo
          case Select(qualifier, _) =>
            Some((Some(qualifier), tree.symbol, Nil, Nil))

          // foo(args)
          case Apply(id: Ident, args) =>
            Some((None, id.symbol, Nil, args))

          // a.foo(args)
          case Apply(s @ Select(qualifier, _), args) =>
            Some((Some(qualifier), s.symbol, Nil, args))

          // foo[T]
          case TypeApply(id: Ident, tps) =>
            Some((None, id.symbol, tps, Nil))

          // a.foo[T]
          case TypeApply(s @ Select(t, _), tps) =>
            Some((Some(t), s.symbol, tps, Nil))

          case Apply(ExCall(caller, sym, tps, args), newArgs) =>
            Some((caller, sym, tps, args ++ newArgs))

          case TypeApply(ExCall(caller, sym, tps, args), newTps) =>
            Some((caller, sym, tps ++ newTps, args))

          case _ => None
        }

        res.map { case (rec, sym, tps, args) =>
          val newRec = rec.filter(r => r.symbol == null || (!r.symbol.isModule && !r.symbol.isModuleClass))
          (newRec, sym, tps, args)
        }
      }
    }

    object ExUpdate {
      def unapply(tree: Apply): Option[(Tree, Tree, Tree)] = tree match {
        case Apply(
              s @ Select(lhs, update),
              index :: newValue :: Nil) if s.symbol.fullName.endsWith("Array.update") =>
            Some((lhs, index, newValue))
        case _ => None
      }
    }

    object ExArrayFill {
      def unapply(tree: Apply): Option[(Tree, Tree, Tree)] = tree match {
        case Apply(
               Apply(
                 Apply(
                   TypeApply(ExSelected("scala", "Array", "fill"), baseType :: Nil),
                   length :: Nil
                 ),
                 defaultValue :: Nil
               ),
               manifest
             ) =>
            Some((baseType, length, defaultValue))
        case _ => None
      }
    }
  }
}
