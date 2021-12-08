/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.scalac

import scala.tools.nsc._
import scala.collection.mutable.{Map => MutableMap}

/** Contains extractors to pull-out interesting parts of the Scala ASTs. */
trait ASTExtractors(val global: Global) {
  import global._
  import global.definitions._

  def classFromName(str: String) = {
    rootMirror.getClassByName(str)
  }

  def objectFromName(str: String) = {
    rootMirror.getClassByName(str)
  }

  /**
   * Extract the annotations for [[sym]], combined with its owner (unless
   * [[ignoreOwner]] is true).
   *
   * When [[sym]] is synthetically created by the compiler, also extract the
   * companion symbol's annotations. But behold the dark arcane magic:
   * [[Symbol.companionSymbol]] is deprecated in favor of [[Symbol.companion]],
   * yet for implicit class the synthetic function of the same name doesn't
   * have a [[Symbol.companion]]. Additionally, the documentation doesn't
   * clearly guarantees that functions can have a companion symbol. In
   * practice, however, it seems to work.
   */
  def getAnnotations(sym: Symbol, ignoreOwner: Boolean = false): Seq[(String, Seq[Tree])] = {
    val actualSymbol = sym.accessedOrSelf.orElse(sym)
    val selfs = actualSymbol.annotations
    val owners =
      if (ignoreOwner) Set.empty
      else actualSymbol.owner.annotations.filter(annot =>
        annot.toString != "stainless.annotation.export" &&
        !annot.toString.startsWith("stainless.annotation.cCode.global")
      )
    val companions = if (actualSymbol.isSynthetic) actualSymbol.companionSymbol.annotations else Set.empty
    (for {
      a <- (selfs ++ owners ++ companions)
      name = a.atp.safeToString
        .replace(".package.", ".")
        .replace(" @scala.annotation.meta.field", "")
    } yield {
      if (name startsWith "stainless.annotation.") {
        val shortName = name drop "stainless.annotation.".length
        Some(shortName, a.args)
      } else if (name == "inline") {
        Some(name, a.args)
      } else {
        None
      }
    }).flatten.foldLeft[(Set[String], Seq[(String, Seq[Tree])])]((Set(), Seq())) {
      case (acc @ (keys, _), (key, _)) if keys contains key => acc
      case ((keys, seq), (key, args)) => (keys + key, seq :+ (key -> args))
    }._2
  }

  protected lazy val scalaMapSym  = classFromName("scala.collection.immutable.Map")
  protected lazy val scalaSetSym  = classFromName("scala.collection.immutable.Set")
  protected lazy val scalaListSym = classFromName("scala.collection.immutable.List")

  protected lazy val exceptionSym = classFromName("stainless.lang.Exception")

  protected lazy val setSym        = classFromName("stainless.lang.Set")
  protected lazy val mapSym        = classFromName("stainless.lang.Map")
  protected lazy val mutableMapSym = classFromName("stainless.lang.MutableMap")
  protected lazy val bagSym        = classFromName("stainless.lang.Bag")
  protected lazy val realSym       = classFromName("stainless.lang.Real")

  protected lazy val bvSym         = classFromName("stainless.math.BitVectors.BV")

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
    require(0 <= i && i <= 22, s"$i must be between 0 and 22")
    classFromName("scala.Function" + i)
  }

  def isTuple(sym: Symbol, size: Int): Boolean = (size > 0 && size <= 22) && (sym == classFromName(s"scala.Tuple$size"))

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

  def isBVSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == bvSym
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

  def isMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == mapSym
  }

  def isMutableMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == mutableMapSym
  }

  def isFunction(sym: Symbol, i: Int) : Boolean =
    0 <= i && i <= 22 && sym == functionTraitSym(i)

  def isArrayClassSym(sym: Symbol): Boolean = sym == arraySym

  private lazy val bvtypes = Set(ByteTpe, ShortTpe, IntTpe, LongTpe)

  def hasBVType(t: Tree) = bvtypes contains t.tpe.widen

  def hasNumericType(t: Tree): Boolean = hasBigIntType(t) || hasBVType(t) || hasRealType(t)

  def hasBigIntType(t: Tree) = isBigIntSym(t.tpe.typeSymbol)

  def hasStringType(t: Tree) = isStringSym(t.tpe.typeSymbol)

  def hasRealType(t: Tree) = isRealSym(t.tpe.typeSymbol)

  def hasBooleanType(t: Tree) = t.tpe.widen =:= BooleanClass.tpe

  def isDefaultGetter(sym: Symbol) = sym.isSynthetic && (sym.name containsName nme.DEFAULT_GETTER_STRING)

  def isCopyMethod(sym: Symbol) = sym.isSynthetic && sym.name == nme.copy

  def canExtractSynthetic(sym: Symbol) = {
    sym.isImplicit ||
    isDefaultGetter(sym) ||
    isCopyMethod(sym)
  }

  object TupleSymbol {
    // It is particularly time expensive so we cache this.
    private val cache = MutableMap[Symbol, Option[Int]]()
    private val cardinality = """Tuple(\d{1,2})""".r
    def unapply(sym: Symbol): Option[Int] = cache.getOrElseUpdate(sym, {
      // First, extract a gess about the cardinality of the Tuple.
      // Then, confirm that this is indeed a regular Tuple.
      val name = sym.unexpandedName.toString
      name match {
        case cardinality(i) if isTuple(sym, i.toInt) => Some(i.toInt)
        case _ => None
      }
    })

    def unapply(tpe: Type): Option[Int] = tpe.typeSymbol match {
      case TupleSymbol(i) => Some(i)
      case _ => None
    }

    def unapply(tree: Tree): Option[Int] = unapply(tree.tpe)
  }

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
          Some(Seq(scalaName.toString, symName(select, name)))

        case Select(from: Select, name) =>
          unapplySeq(from).map(prefix => prefix :+ symName(select, name))

        case Select(from: Ident, name) =>
          val full = symName(select, name) :: from.symbol.ownerChain.init.map(_.name.toString)
          Some(full.reverse)

        case _ =>
          None
      }
    }
  }

  object StructuralExtractors {
    import ExtractorHelpers._

    /** Extracts the 'ensuring' contract from an expression. */
    object ExEnsuredExpression {
      def unapply(tree: Apply): Option[(Tree,Tree,Boolean)] = tree match {
        case Apply(Select(Apply(TypeApply(
              ExSelected("scala", "Predef", "Ensuring"),
              _ :: Nil), body :: Nil), ExNamed("ensuring")), contract :: Nil)
          => Some((body, contract, false))

        case Apply(Select(Apply(TypeApply(
              ExSelected("stainless", "lang", "StaticChecks", "Ensuring"),
              _ :: Nil), body :: Nil), ExNamed("ensuring")), contract :: Nil)
          => Some((body, contract, true))

        case _ => None
      }
    }

    object ExThrowingExpression {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(Apply(
          TypeApply(ExSelected("stainless", "lang", "`package`", "Throwing"), _ :: Nil), body :: Nil), ExNamed("throwing")),
          contract :: Nil
        ) => Some((body, contract))

        case _ =>None
      }
    }

    /** Matches the `holds` expression at the end of any boolean expression, and returns the boolean expression.*/
    object ExHoldsExpression {
      def unapply(tree: Select) : Option[Tree] = tree match {
        case Select(
          Apply(ExSelected("stainless", "lang", "`package`", "BooleanDecorations"), realExpr :: Nil),
          ExNamed("holds")
        ) => Some(realExpr)
        case _ => None
       }
    }

    /** Matches the `holds` expression at the end of any boolean expression with a proof as argument, and returns both of themn.*/
    object ExHoldsWithProofExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(Apply(ExSelected("stainless", "lang", "`package`", "BooleanDecorations"), body :: Nil), ExNamed("holds")), proof :: Nil) =>
          Some((body, proof))
        case _ => None
       }
    }

    /** Matches the `because` method at the end of any boolean expression, and return the assertion and the cause. If no "because" method, still returns the expression */
    object ExMaybeBecauseExpressionWrapper {
      def unapply(tree: Tree) : Some[Tree] = tree match {
        case Apply(ExSelected("stainless", "lang", "`package`", "because"), body :: Nil) =>
          unapply(body)
        case body => Some(body)
       }
    }

    /** Matches the `because` method at the end of any boolean expression, and return the assertion and the cause.*/
    object ExBecauseExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(
          Apply(ExSelected("stainless", "proof" | "equations", "`package`", "boolean2ProofOps"), body :: Nil),
          ExNamed("because")), proof :: Nil) => Some((body, proof))
        case _ => None
       }
    }

    /** Matches the `bigLength` expression at the end of any string expression, and returns the expression.*/
    object ExBigLengthExpression {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case Apply(Select(
          Apply(ExSelected("stainless", "lang", "`package`", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigLength")), Nil)
          => Some(stringExpr)
        case _ => None
       }
    }

    /** Matches the `bigSubstring` method at the end of any string expression, and returns the expression and the start index expression.*/
    object ExBigSubstringExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(
          Apply(ExSelected("stainless", "lang", "`package`", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigSubstring")), startExpr :: Nil)
           => Some(stringExpr, startExpr)
        case _ => None
       }
    }

    /** Matches the `bigSubstring` expression at the end of any string expression, and returns the expression, the start and end index expressions.*/
    object ExBigSubstring2Expression {
      def unapply(tree: Apply) : Option[(Tree, Tree, Tree)] = tree match {
        case Apply(Select(
          Apply(ExSelected("stainless", "lang", "`package`", "StringDecorations"), stringExpr :: Nil),
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

    /** Matches `lhs &&& rhs` and returns (lhs, rhs)*/
    object ExSplitAnd {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case
          Apply(
            Select(
              Apply(
                ExSymbol("stainless", "lang", "BooleanDecorations"),
                lhs :: Nil
              ),
              ExNamed("$amp$amp$amp")
            ),
            rhs :: Nil
          ) => Some((lhs, rhs))
        case _ => None
      }
    }

    /** Extracts the 'require' contract from an expression (only if it's the
     * first call in the block). */
    object ExRequiredExpression {
      def unapply(tree: Apply): Option[(Tree, Boolean)] = tree match {
        case Apply(ExSelected("scala", "Predef", "require"), contractBody :: Nil) =>
          Some((contractBody, false))

        case Apply(ExSelected("stainless", "lang", "StaticChecks", "require"), contractBody :: Nil) =>
          Some((contractBody, true))

        case _ => None
      }
    }

    /** Extracts the 'reads' contract from an expression */
    object ExReadsExpression {
      def unapply(tree: Apply): Option[Tree] = tree match {
        case Apply(ExSelected("stainless", "lang", "`package`", "reads"), objs :: Nil) =>
          Some(objs)
        case _ => None
      }
    }

    /** Extracts the 'modifies' contract from an expression */
    object ExModifiesExpression {
      def unapply(tree: Apply): Option[Tree] = tree match {
        case Apply(ExSelected("stainless", "lang", "`package`", "modifies"), objs :: Nil) =>
          Some(objs)
        case _ => None
      }
    }

    /** Extracts the 'decreases' contract for an expression (should be right after 'require') */
    object ExDecreasesExpression {
      def unapply(tree: Apply): Option[Seq[Tree]] = tree match {
        case Apply(ExSelected("stainless", "lang", "`package`", "decreases"), args) =>
          Some(args)
        case _ => None
      }
    }

    /** Matches the `A computes B` expression at the end of any expression A, and returns (A, B). */
    object ExComputesExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(
          Apply(TypeApply(ExSelected("stainless", "lang", "`package`", "SpecsDecorations"), List(_)), realExpr :: Nil),
          ExNamed("computes")), expected::Nil)
         => Some((realExpr, expected))
        case _ => None
       }
    }

    /** Extracts the `(input, output) passes { case In => Out ...}`
     *  and returns (input, output, list of case classes) */
    object ExPasses {
      import ExpressionExtractors._

      def unapply(tree: Apply): Option[(Tree, Tree, List[CaseDef])] = tree match {
        case Apply(
          Select(
            Apply(
              TypeApply(
                ExSelected("stainless", "lang", "`package`", "Passes"),
                Seq(_, _)
              ),
              Seq(ExTuple(_, Seq(in, out)))
            ),
            ExNamed("passes")
          ),
          Seq(ExLambdaExpression(
            Seq(ValDef(_, _, _, EmptyTree)),
            ExPatternMatching(_, tests)
          ))
        ) => Some((in, out, tests))
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
        case Apply(ExSelected("scala", "`package`", "BigInt", "apply"), n :: Nil) =>
          Some(n)
        case Apply(ExSelected("stainless", "lang", "`package`", "BigInt", "apply"), n :: Nil) =>
          Some(n)
        case _ =>
          None
      }
    }

    object FrontendBVType {
      val R = """type (UInt|Int)(\d+)""".r

      def unapply(tpe: Type): Option[(Boolean, Int)] = tpe match {
        case TypeRef(_, sym, FrontendBVKind(signed, size) :: Nil) if isBVSym(sym) =>
          Some((signed, size))
        case TypeRef(_, sym, Nil) if isBVSym(sym) =>
          sym.toString match {
            case R(signed, size) => Some((signed == "Int", size.toInt))
            case _ => None
          }
        case _ => FrontendBVKind.unapply(tpe)
      }

      def unapply(tr: Tree): Option[(Boolean, Int)] = unapply(tr.tpe)
    }

    object FrontendBVKind {
      val R = """object ([ui])(\d+)""".r

      def unapply(tpe: Type): Option[(Boolean, Int)] = tpe match {
        case SingleType(_, sym) =>
          sym.toString match {
            case R(signed, size) => Some((signed == "i", size.toInt))
            case _ => None
          }
        case _ =>
          None
      }

      def unapply(tr: Tree): Option[(Boolean, Int)] = unapply(tr.tpe)
    }

    /** `max` extraction for bitvectors */
    object ExMaxBV {
      def unapply(tree: Tree): Option[(Boolean, Int)] = tree  match {
        case TypeApply(
          ExSelected("stainless", "math", "BitVectors", "max"),
          FrontendBVType(signed, size) :: Nil
        ) =>
          Some((signed, size))
        case _ =>
          None
      }
    }

    /** `min` extraction for bitvectors */
    object ExMinBV {
      def unapply(tree: Tree): Option[(Boolean, Int)] = tree  match {
        case TypeApply(
          ExSelected("stainless", "math", "BitVectors", "min"),
          FrontendBVType(signed, size) :: Nil
        ) =>
          Some((signed, size))
        case _ =>
          None
      }
    }

    /** `fromByte` extraction (Byte to Int8 identity conversion) */
    object ExFromByte {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(
          ExSelected("stainless", "math", "BitVectors", "fromByte"),
          expr :: Nil
        ) =>
          Some(expr)
        case _ =>
          None
      }
    }

    /** `fromShort` extraction (Short to Int16 identity conversion) */
    object ExFromShort {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(
          ExSelected("stainless", "math", "BitVectors", "fromShort"),
          expr :: Nil
        ) =>
          Some(expr)
        case _ =>
          None
      }
    }

    /** `fromInt` extraction (Int to Int32 identity conversion) */
    object ExFromInt {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(
          ExSelected("stainless", "math", "BitVectors", "fromInt"),
          expr :: Nil
        ) =>
          Some(expr)
        case _ =>
          None
      }
    }

    /** `fromLong` extraction (Long to Int64 identity conversion) */
    object ExFromLong {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(
          ExSelected("stainless", "math", "BitVectors", "fromLong"),
          expr :: Nil
        ) =>
          Some(expr)
        case _ =>
          None
      }
    }

    /** `intToBV` extraction */
    object ExIntToBV {
      def unapply(tree: Tree): Option[(Tree, Tree)] = tree  match {
        case Apply(
          TypeApply(
            ExSelected("stainless", "math", "BitVectors", "intToBV"),
            typ :: Nil
          ), n :: Nil
        ) =>
          Some((typ, n))
        case _ =>
          None
      }
    }

    /** `bigIntToBV` extraction */
    object ExBigIntToBV {
      def unapply(tree: Tree): Option[(Boolean, Int, Tree)] = tree  match {
        case Apply(
          TypeApply(
            ExSelected("stainless", "math", "BitVectors", "bigIntToBV"),
            FrontendBVKind(signed, size) :: Nil
          ), n :: Nil
        ) =>
          Some((signed, size, n))
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

    /** Matches the construct stainless.math.wrapping[A](a) and returns a */
    object ExWrapping {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(TypeApply(ExSelected("stainless", "math", "`package`", "wrapping"), Seq(_)), tree :: Nil) =>
          Some(tree)
        case _ =>
          None
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
      def unapply(tree: Apply): Option[(Tree, Option[String], Boolean)] = tree match {
        case Apply(ExSymbol("scala", "Predef", "assert"), contractBody :: Nil) =>
          Some((contractBody, None, false))

        case Apply(ExSymbol("stainless", "lang", "StaticChecks", "assert"), contractBody :: Nil) =>
          Some((contractBody, None, true))

        case Apply(
            ExSymbol("scala", "Predef", "assert"), contractBody :: (error: Literal) :: Nil) =>
          Some((contractBody, Some(error.value.stringValue), false))

        case Apply(ExSymbol("stainless", "lang", "StaticChecks", "assert"), contractBody :: (error: Literal) :: Nil) =>
          Some((contractBody, Some(error.value.stringValue), true))

        case _ =>
          None
      }
    }

    /** Matches an object with no type parameters, regardless of its visibility. */
    object ExObjectDef {
      def unapply(md: ModuleDef): Option[(String, Template)] = md match {
        case ModuleDef(_, name, impl) if !md.symbol.isCase => Some((name.toString, impl))
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
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if name.toString == "main" && tparams.isEmpty && vparamss.size == 1 && vparamss.head.size == 1 =>
          true
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
            !(getAnnotations(tpt.symbol) exists (_._1 == "ignore"))
          ) ||
            !dd.symbol.isSynthetic ||
            canExtractSynthetic(dd.symbol)
          ) {
            Some((dd.symbol, tparams.map(_.symbol), vparamss.flatten, tpt.tpe, rhs))
          } else {
            None
          }
        case _ => None
      }
    }

    object ExMutableFieldDef {

      /** Matches a definition of a strict var field inside a class constructor */
      def unapply(vd: ValDef) : Option[(Symbol, Type, Tree)] = {
        val sym = vd.symbol
        vd match {
          // Implemented fields
          case ValDef(mods, name, tpt, rhs) if (
            !sym.isCaseAccessor && !sym.isParamAccessor &&
            !sym.isLazy && !sym.isSynthetic && sym.isVar
          ) =>
            // Since scalac uses the accessor symbol all over the place, we pass that instead:
            Some((sym, tpt.tpe, rhs))
          case _ => None
        }
      }
    }

    object ExFieldDef {
      /** Matches a definition of a strict field */
      def unapply(vd: ValDef): Option[(Symbol, Type, Tree)] = {
        val sym = vd.symbol
        vd match {
          // Implemented fields
          case ValDef(mods, name, tpt, rhs) if (
            !sym.isCaseAccessor && !sym.isParamAccessor &&
            !sym.isLazy && !sym.isSynthetic && !sym.isVar
          ) =>
            Some((sym, tpt.tpe, rhs))
          case _ => None
        }
      }
    }

    object ExLazyFieldDef {
      /** Matches a definition of a lazy field */
      def unapply(vd: ValDef): Option[(Symbol, Type, Tree)] = {
        val sym = vd.symbol
        vd match {
          case ValDef(mods, name, tpt, rhs) if (
            sym.isLazy && !sym.isCaseAccessor && !sym.isParamAccessor &&
            !sym.isSynthetic
          ) =>
            Some((sym, tpt.tpe, rhs))
          case _ => None
        }
      }
    }

    object ExFieldAccessorFunction {
      /** Matches the accessor function of a field */
      def unapply(dd: DefDef): Option[(Symbol, Type, Seq[ValDef], Tree)] = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(
          vparamss.size <= 1 && name != nme.CONSTRUCTOR &&
          dd.symbol.isAccessor && !dd.symbol.isLazy
        ) =>
          Some((dd.symbol, tpt.tpe, vparamss.flatten, rhs))
        case _ => None
      }
    }

    object ExLazyFieldAccessorFunction {
      def unapply(dd: DefDef): Option[(Symbol, Type, Tree)] = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(
          vparamss.size <= 1 && name != nme.CONSTRUCTOR &&
          !dd.symbol.isSynthetic && dd.symbol.isAccessor && dd.symbol.isLazy
        ) =>
          Some((dd.symbol, tpt.tpe, rhs))
        case _ => None
      }
    }

    object ExIndexedAt {
      def unapply(annot: Annotation): Option[Tree] = annot match {
        case AnnotationInfo(TypeRef(_, sym, _), Seq(arg), _) if
            getResolvedTypeSym(sym) == classFromName("stainless.annotation.indexedAt") =>
          Some(arg)
        case _ => None
      }
    }
  }

  object ExpressionExtractors {
    import ExtractorHelpers._

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

    object ExSnapshotExpression {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "snapshot"), List(_)), List(arg)) =>
          Some(arg)
        case _ =>
          None
      }
    }

    object ExFreshCopyExpression {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "freshCopy"), List(_)), List(arg)) =>
          Some(arg)
        case _ =>
          None
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

    object ExSwapExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree, Tree, Tree)] = tree match {
        case a @ Apply(
              TypeApply(ExSymbol("stainless", "lang", "swap"), _),
              array1 :: index1 :: array2 :: index2 :: Nil) =>
            Some((array1, index1, array2, index2))
        case _ => None
      }
    }

    object ExLambdaExpression {
      def unapply(tree: Function) : Some[(Seq[ValDef], Tree)] = tree match {
        case Function(vds, body) => Some((tree.vparams, tree.body))
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

    private object ExArraySelect {
      def unapply(tree: Select): Option[(Tree, String)] = tree match {
        case Select(array, select) if isArrayClassSym(array.tpe.typeSymbol) => Some((array, select.toString))
        case _ => None
      }
    }

    /**
     * Extract both Array.length and Array.size as they are equivalent.
     *
     * Note that Array.size is provided thought implicit conversion to
     * scala.collection.mutable.ArrayOps via scala.Predef.*ArrayOps.
     * As such, `arrayOps` can be `intArrayOps`, `genericArrayOps`, etc...
     */
    object ExArrayLength {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(Apply(ExSymbol("scala", "Predef", arrayOps), Seq(array)), size)
             if (arrayOps.toString endsWith "ArrayOps") && (size.toString == "size")
             => Some(array)

        case ExArraySelect(array, "length") => Some(array)

        case _ => None
      }
    }

    object ExArrayApplyBV {
      def unapply(tree: Apply): Option[(Tree, Tree, Tree)] = tree match {
        case Apply(TypeApply(
          Select(
            Apply(
              TypeApply(ExSelected("stainless", "math", "BitVectors", "ArrayIndexing"), tpe :: Nil),
              array :: Nil
            ),
            ExNamed("apply")
          ),
          bvType :: Nil),
          index :: Nil) =>

          Some((array, bvType, index))

        case _ => None
      }
    }

    object ExArrayUpdated {
      def unapply(tree: Apply): Option[(Tree, Tree, Tree)] = tree match {
        case Apply(
               Apply(
                 TypeApply(Select(Apply(ExSymbol("scala", "Predef", arrayOps), Seq(array)), update), _),
                 Seq(index, value)),
               List(Typed(_, _))
             )
             if (arrayOps endsWith "ArrayOps") && (update.toString == "updated")
             => Some((array, index, value))

        case Apply(
          Select(
            Apply(
              TypeApply(ExSelected("stainless", "lang", "`package`", "ArrayUpdating"), tpe :: Nil),
              array :: Nil
            ),
            ExNamed("updated")
          ),
          index :: value :: Nil) =>

          Some((array, index, value))

        // There's no `updated` method in the Array class itself, only though implicit conversion.
        case _ => None
      }
    }

    object ExArrayUpdate {
      def unapply(tree: Apply): Option[(Tree, Tree, Tree)] = tree match {
        // This implicit conversion to ArrayOps is shadowed. We therefore skip it here.
        case Apply(ExArraySelect(array, "update"), Seq(index, newValue)) => Some((array, index, newValue))
        case _ => None
      }
    }

    object ExArrayApply {
      def unapply(tree: Apply): Option[(Tree, Tree)] = tree match {
        // This implicit conversion to ArrayOps is shadowed. We therefore skip it here.
        case Apply(ExArraySelect(array, "apply"), Seq(index)) => Some((array, index))
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

    object ExFieldAssign {
      def unapply(tree: Assign): Option[(Symbol,Tree,Tree)] = tree match {
        case Assign(sel@Select(This(_), v), rhs) => Some((sel.symbol, sel, rhs))
        case _ => None
      }
    }

    object ExBareWhile {
      def unapply(tree: LabelDef): Option[(Tree,Tree)] = tree match {
        case (label@LabelDef(
                _, _, If(cond, Block(body, jump@Apply(_, _)), unit@ExUnitLiteral())))
              if label.symbol == jump.symbol && unit.symbol == null => Some((cond, Block(body, unit)))
        case _ => None
      }
    }

    object ExWhile {
      object WithInvariant {
        def unapply(tree: Tree): Option[(Tree, Tree)] = tree match {
          case Apply(
            Select(
              Apply(while2invariant, List(rest)),
              invariantSym),
            List(invariant)) if invariantSym.toString == "invariant" => Some((invariant, rest))
          case _ => None
        }
      }

      object WithWeakInvariant {
        def unapply(tree: Tree): Option[(Tree, Tree)] = tree match {
          case Apply(
            Select(
              Apply(while2invariant, List(rest)),
              invariantSym),
            List(invariant)) if invariantSym.toString == "noReturnInvariant" => Some((invariant, rest))
          case _ => None
        }
      }

      object WithInline {
        def unapply(tree: Tree): Option[Tree] = tree match {
          case Select(
              Apply(_, List(rest)),
              inlineSym
            ) if inlineSym.toString == "inline" => Some(rest)
          case _ => None
        }
      }

      object WithOpaque {
        def unapply(tree: Tree): Option[Tree] = tree match {
          case Select(
              Apply(_, List(rest)),
              opaqueSym
            ) if opaqueSym.toString == "opaque" => Some(rest)
          case _ => None
        }
      }


      def parseWhile(tree: Tree, optInv: Option[Tree], optWeakInv: Option[Tree], inline: Boolean, opaque: Boolean):
        Option[(Tree, Tree, Option[Tree], Option[Tree], Boolean, Boolean)] = {

        tree match {
          case WithOpaque(rest) => parseWhile(rest, optInv, optWeakInv, inline, true)
          case WithInline(rest) => parseWhile(rest, optInv, optWeakInv, true, opaque)
          case WithInvariant(invariant, rest) => parseWhile(rest, Some(invariant), optWeakInv, inline, opaque)
          case WithWeakInvariant(invariant, rest) => parseWhile(rest, optInv, Some(invariant), inline, opaque)
          case ExBareWhile(cond, body) => Some((cond, body, optInv, optWeakInv, inline, opaque))
          case _ => None
        }
      }

      // returns condition, body, optional invariant and weak invariant, inline boolean, opaque boolean
      def unapply(tree: Tree): Option[(Tree, Tree, Option[Tree], Option[Tree], Boolean, Boolean)] =
        parseWhile(tree, None, None, false, false)
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

        case Apply(TypeApply(e, tps), args) if
          isTuple(e.symbol.owner.companionClass, args.size) &&
          e.symbol.name.toString == "apply" => Some((tps.map(_.tpe), args))

        case _ => None
      }
    }

    object ExIdentity {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case Apply(TypeApply(ExSelected("scala", "Predef", "identity"), _), List(body)) =>
          Some(body)
        case Apply(TypeApply(ExSelected("scala", "Predef", "locally"), _), List(body)) =>
          Some(body)
        case _ =>
          None
      }
    }

    object ExTupleExtract {
      def unapply(tree: Select) : Option[(Tree,Int)] = tree match {
        case Select(lhs @ TupleSymbol(i), n) =>
          val methodName = n.toString
          if(methodName.head == '_') {
            val indexString = methodName.tail
            try {
              val index = indexString.toInt
              if(index > 0 && index <= i) {
                Some((lhs, index))
              } else None
            } catch {
              case t: Throwable =>
                None
            }
          } else None
        case _ => None
      }
    }

    object ExIfThenElse {
      def unapply(tree: If): Option[(Tree,Tree,Tree)] = tree match {
        case If(t1,t2,t3) => Some((t1,t2,t3))
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
      def unapply(tree: Tree): Option[(Type, Seq[Tree])] = tree match {
        case Apply(s @ Select(New(tpt), n), args) if n == nme.CONSTRUCTOR =>
          Some((tpt.tpe, args))

        case Apply(e, args) if (
          (e.symbol.owner.isModuleClass) &&
          (e.symbol.isSynthetic) &&
          (e.symbol.name.toString == "apply")
        ) => Some((tree.tpe, args))

        case _ => None
      }
    }

    object ExIdentifier {
      def unapply(tree: Ident): Option[(Symbol,Tree)] = tree match {
        case i: Ident => Some((i.symbol, i))
      }
    }

    object ExTyped {
      def unapply(tree : Typed): Option[(Tree,Tree)] = tree match {
        case Typed(e,t) => Some((e,t))
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
        case ua @ UnApply(Apply(ExSelected("stainless", "lang", "`package`", "BigInt", "unapply"), _), List(l)) =>
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

    object ExMutableMapWithDefault {
      def unapply(tree: Apply): Option[(Tree,Tree,Tree)] = tree match {
        case Apply(TypeApply(ExSelected("MutableMap", "withDefaultValue"), Seq(tptFrom, tptTo)), Seq(default)) =>
          Some(tptFrom, tptTo, default)
        case Apply(TypeApply(ExSelected("stainless", "lang", "MutableMap", "withDefaultValue"), Seq(tptFrom, tptTo)), Seq(default)) =>
          Some(tptFrom, tptTo, default)
        case _ => None
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
          val newRec = rec.filter {
            case r if r.symbol == null => true
            case r if (r.symbol.isModule || r.symbol.isModuleClass) && !r.symbol.isCase => false
            case r => true
          }

          (newRec, sym, tps, args)
        }
      }
    }
  }
}
