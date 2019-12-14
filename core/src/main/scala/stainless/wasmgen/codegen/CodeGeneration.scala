/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package wasmgen
package codegen

import intermediate.{trees => t}
import wasm._
import Expressions.{eq => EQ, _}
import Types._
import Definitions._

trait CodeGeneration {

  /* Environments */
  protected case class FunEnv(
    s: t.Symbols,
    gh: GlobalsHandler,
    dh: DataHandler,
    tab: Table
  ) {
    def env(lh: LocalsHandler): Env = Env(s, lh, gh, dh, tab)
  }
  protected case class Env(
    s: t.Symbols,
    lh: LocalsHandler,
    gh: GlobalsHandler,
    dh: DataHandler,
    tab: Table
  ) {
    def fEnv = FunEnv(s, gh, dh, tab)
  }

  // Make fresh labels using stainless identifiers
  final protected def freshLabel(s: String): String = FreshIdentifier(s).uniqueName

  final protected val lib: LibProvider { val trees: t.type } = new LibProvider {
    protected val trees = t
  }

  /* Generate parts of the module */
  protected def mkImports(symbols: t.Symbols): Seq[Import] = {
    Seq(Import("system", "printString", FunSig("_printString_", Seq(i32), void)))
  }
  protected def mkGlobals(s: t.Symbols): Seq[ValDef]
  /* Called after the functions are created to update the initial values of the globals */
  protected def updateGlobals(env: FunEnv): Unit
  protected def mkTable(s: t.Symbols) = Table(
    s.functions.values.toList.filter(_.flags.contains(t.Dynamic)).map(_.id.uniqueName)
  )
  protected def mkBuiltins(s: t.Symbols, toExecute: Seq[Identifier])(implicit funEnv: FunEnv): Seq[FunDef] = {
    Seq(
      mkMain(s, toExecute),
      mkEquality(s), mkInequality(s),
      mkFloatToSign(f32), mkFloatToSign(f64),
      mkToString(s), mkBigIntToString, mkArrayToString, mkCharToString,
      mkStringConcat, mkSubstring
    )
  }

  /* Built-in functions */
  final protected val stringConcatName = "_string_concat_"
  final protected val substringName = "_substring_"
  final protected val refEqualityName = "_ref_eq_"
  final protected val refInequalityName = "_ref_ineq_"
  final protected val refToStringName = "_ref_toString_"
  final protected def arrayCopyName(tpe: Type) = s"_array_copy_${tpe}_"
  final protected def floatToSignName(tpe: Type) = s"_${tpe}_sign_"
  protected val builtinToStrings: Set[String]
  final protected def toStringName(name: String)(implicit funEnv: FunEnv): String = {
    val fullName = s"${name}ToString"
    if (builtinToStrings contains name) fullName
    else lib.fun(fullName)(funEnv.s).id.uniqueName
  }
  private def mkFloatToSign(tpe: Type) = {
    require(tpe == f32 || tpe == f64)
    FunDef(floatToSignName(tpe), Seq(ValDef("lhs", tpe), ValDef("rhs", tpe)), i32) { implicit lh =>
      val lhs = GetLocal("lhs")
      val rhs = GetLocal("rhs")
      If(
        freshLabel("label"),
        gt(lhs, rhs),
        I32Const(1),
        If(
          freshLabel("label"),
          lt(lhs, rhs),
          I32Const(-1),
          I32Const(0)
        )
      )
    }
  }
  private def mkMain(s: t.Symbols, toExecute: Seq[Identifier])(implicit funEnv: FunEnv): FunDef = {
    FunDef("_main_", Seq(), void) { lh =>
      transform(t.sequence(
        toExecute map { fid =>
          t.Output(t.StringConcat(
            t.StringLiteral(s"${fid.name} = "),
            t.FunctionInvocation(lib.fun("toString")(funEnv.s).id, Seq(),
              Seq(t.FunctionInvocation(fid, Seq(), Seq())))
          ))
        }
      ))(funEnv.env(lh))
    }
  }
  /* Abstract builtins (related to ref. types) */
  protected def mkEquality(s: t.Symbols): FunDef
  protected def mkInequality(s: t.Symbols): FunDef
  protected def mkToString(s: t.Symbols)(implicit funEnv: FunEnv): FunDef
  protected def mkCharToString(implicit funEnv: FunEnv): FunDef
  protected def mkBigIntToString(implicit funEnv: FunEnv): FunDef
  protected def mkArrayToString(implicit funEnv: FunEnv): FunDef
  protected def mkStringConcat(implicit funEnv: FunEnv): FunDef
  protected def mkSubstring(implicit funEnv: FunEnv): FunDef

  /** Transform a stainless Symbols into a wasm Module */
  final def transform(s: t.Symbols, toExecute: Seq[Identifier]): Module = {
    val imports = mkImports(s)
    val globals = mkGlobals(s)
    val tab = mkTable(s)
    Module("program", imports, globals, tab){ (gh, dh) =>
      implicit val funEnv = FunEnv(s, gh, dh, tab)
      val funs = mkBuiltins(s, toExecute) ++ s.functions.values.toList.map(transform)
      updateGlobals(funEnv)
      funs
    }
  }

  /** Transform a stainless FunDef to a wasm FunDef */
  final def transform(fd: t.FunDef)(implicit env: FunEnv): FunDef = {
    implicit val s = env.s
    FunDef(
      fd.id.uniqueName,
      fd.params.map(arg => ValDef(arg.id.uniqueName, transform(arg.tpe))).filterNot(_.tpe == void),
      transform(fd.returnType)
    ) { lh =>
      transform(fd.fullBody)(env.env(lh))
    }
  }

  /* Expr. Helpers */

  final protected def typeToSign(tpe: t.Typed)(implicit s: t.Symbols): Sign = {
    tpe.getType match {
      case t.BVType(false, _) => Unsigned
      case _ => Signed
    }
  }

  final protected def typeToOp(tpe: t.Typed, intOp: Sign => BinOp, floatOp: BinOp)(implicit s: t.Symbols): BinOp = {
    tpe.getType match {
      case t.RealType() => floatOp
      case t.BVType(false, _) => intOp(Unsigned)
      case _ => intOp(Signed)
    }
  }

  final protected def mkBin(op: BinOp, lhs: t.Expr, rhs: t.Expr)(implicit env: Env): Expr = {
    op(transform(lhs), transform(rhs))
  }

  final protected def surfaceEq(lhs: Expr, rhs: Expr, tpe: t.Type): Expr = {
    tpe match {
      case t.RecordType(_) =>
        Call(refEqualityName, i32, Seq(lhs, rhs))
      case t.UnitType() =>
        I32Const(1)
      case _ =>
        EQ(lhs, rhs)
    }
  }
  final protected def surfaceIneq(lhs: Expr, rhs: Expr, tpe: t.Type): Expr =
    tpe match {
      case t.RecordType(_) =>
        Call(refInequalityName, i32, Seq(lhs, rhs))
      case t.UnitType() =>
        I32Const(0)
      case _ =>
        baseTypeIneq(lhs, rhs)
    }
  final protected def baseTypeIneq(lhs: Expr, rhs: Expr): Expr =
    lhs.getType match {
      case `f32` =>
        Call(floatToSignName(f32), i32, Seq(lhs, rhs))
      case `f64` =>
        Call(floatToSignName(f64), i32, Seq(lhs, rhs))
      case `i64` =>
        Wrap(i32, sub(lhs, rhs))
      case `i32` =>
        sub(lhs, rhs)
    }

  final protected def surfaceToString(arg: Expr, tpe: t.Type)(implicit funEnv: FunEnv): Expr = {
    tpe match {
      case t.RecordType(_) =>
        Call(refToStringName, i32, Seq(arg))
      case t.UnitType() =>
        Call(toStringName("unit"), i32, Seq())
      case t.BooleanType() =>
        Call(toStringName("boolean"), i32, Seq(arg))
      case t.CharType() =>
        Call(toStringName("char"), i32, Seq(arg))
      case t.StringType() =>
        arg
      case t.ArrayType(_) =>
        Call(toStringName("array"), i32, Seq(arg))
      case t.IntegerType() =>
        Call(toStringName("BigInt"), i32, Seq(arg))
      case _ =>
        Call(toStringName(arg.getType.toString), i32, Seq(arg))
    }
  }


  /* Abstract expression constructors (related to ref. types) */
  protected def mkRecord(recordType: t.RecordType, fields: Seq[Expr])(implicit env: Env): Expr
  protected def mkRecordSelector(expr: Expr, rt: t.RecordType, id: Identifier)(implicit env: Env): Expr
  protected def mkCastDown(expr: Expr, subType: t.RecordType)(implicit env: Env): Expr
  protected def mkCastUp(expr: Expr, superType: t.RecordType)(implicit env: Env): Expr
  protected def mkNewArray(length: Expr, init: Option[Expr])(implicit env: Env): Expr
  protected def mkArrayGet(array: Expr, index: Expr)(implicit env: Env): Expr
  protected def mkArraySet(array: Expr, index: Expr, value: Expr)(implicit env: Env): Expr
  protected def mkArrayLength(expr: Expr)(implicit env: Env): Expr
  protected def mkStringLiteral(s: String)(implicit env: Env): Expr

  /** Transform a stainless Expr into a wasm Expr */
  final def transform(expr: t.Expr)(implicit env: Env): Expr = {
    implicit val lh = env.lh
    implicit val s  = env.s
    val compareId = lib.fun("compare").id
    val toStringId = lib.fun("toString").id
    expr match {
      case t.NoTree(tpe) =>
        Unreachable
      case t.Variable(id, tpe, flags) =>
        if (tpe == t.UnitType()) Nop
        else GetLocal(id.uniqueName)
      case t.Let(vd, value, body) =>
        if (vd.getType == t.UnitType()) {
          Sequence(Seq(transform(value), transform(body)))
        } else {
          val local = lh.getFreshLocal(vd.id.uniqueName, transform(vd.getType))
          Sequence(Seq(
            SetLocal(local, transform(value)),
            transform(body)
          ))
        }
      case t.Output(msg) =>
        Call("_printString_", void, Seq(transform(msg)))
      case t.FunctionInvocation(`compareId`, _, Seq(lhs, rhs)) =>
        surfaceIneq(transform(lhs), transform(rhs), lhs.getType)
      case t.FunctionInvocation(`toStringId`, _, Seq(arg)) =>
        surfaceToString(transform(arg), arg.getType)(env.fEnv)
      case fi@t.FunctionInvocation(id, _, args) =>
        if (args.exists(_.getType == t.UnitType())) {
          val (argComps, argNames) = args.map(arg =>
            if (arg.getType == t.UnitType()) (transform(arg), None)
            else {
              val tmp = lh.getFreshLocal(freshLabel("arg"), transform(arg.getType))
              (SetLocal(tmp, transform(arg)), Some(GetLocal(tmp)))
            }
          ).unzip
          Sequence(
            argComps :+
            Call(id.uniqueName, transform(fi.getType), argNames.flatten)
          )
        } else {
          Call(id.uniqueName, transform(fi.getType), args map transform)
        }
      case t.Sequence(es) =>
        Sequence ( es map transform )

      case t.IfExpr(cond, thenn, elze) =>
        If(
          freshLabel("label"),
          transform(cond),
          transform(thenn),
          transform(elze)
        )
      case t.Equals(lhs, rhs) =>
        surfaceEq(transform(lhs), transform(rhs), lhs.getType)

      case t.UnitLiteral() =>
        Nop
      case bvl@t.BVLiteral(_, _, size) =>
        if (size <= 32) I32Const(bvl.toBigInt.toInt)
        else I64Const(bvl.toBigInt.toLong)
      case t.BooleanLiteral(value) =>
        I32Const(if (value) 1 else 0)
      case t.StringLiteral(str) =>
        mkStringLiteral(str)
      case t.CharLiteral(value) =>
        I32Const(value.toInt)
      case t.IntegerLiteral(value) =>
        // TODO: Represent mathematical integers adequately
        I64Const(
          if (value.isValidLong) value.toLong
          else if (value > Long.MaxValue) Long.MaxValue
          else Long.MinValue
        )
      case t.FractionLiteral(numerator, denominator) =>
        F64Const((BigDecimal(numerator) / BigDecimal(denominator)).toDouble)

      case t.Record(tpe, fields) =>
        mkRecord(tpe, fields map transform)
      case rs@t.RecordSelector(record, selector) =>
        val rt = record.getType.asInstanceOf[t.RecordType]
        mkRecordSelector(transform(record), rt, selector)

      case t.FunctionPointer(id) =>
        I32Const(env.tab.indexOf(id.uniqueName))
      case t.Application(callee, args) =>
        CallIndirect(
          transform(callee.getType.asInstanceOf[t.FunctionType].to),
          transform(callee),
          args map transform
        )

      case t.CastDown(e, subtype) =>
        mkCastDown(transform(e), subtype)
      case t.CastUp(e, supertype) =>
        mkCastUp(transform(e), supertype)

      case t.NewArray(length, init) =>
        mkNewArray(transform(length), init map transform)
      case ag@t.ArraySelect(array, index) =>
        mkArrayGet(transform(array), transform(index))
      case t.ArraySet(array, index, value) =>
        mkArraySet(transform(array), transform(index), transform(value))
      case t.ArrayLength(array) =>
        mkArrayLength(transform(array))

      case t.StringLength(expr) =>
        Extend(i64, Unsigned, mkArrayLength(transform(expr)))
      case t.StringConcat(lhs, rhs) =>
        Call(stringConcatName, i32, Seq(transform(lhs), transform(rhs)))
      case t.SubString(expr, start, end) =>
        Call(substringName, i32, Seq(transform(expr), Wrap(i32, transform(start)), Wrap(i32, transform(end))))

      case t.Plus(lhs, rhs) =>
        mkBin(add, lhs, rhs)
      case t.Minus(lhs, rhs) =>
        mkBin(sub, lhs, rhs)
      case t.Times(lhs, rhs) =>
        mkBin(mul, lhs, rhs)
      case t.Division(lhs, rhs) =>
        mkBin(typeToOp(lhs, div(_), div), lhs, rhs)
      case t.Remainder(lhs, rhs) =>
        mkBin(rem(typeToSign(lhs)), lhs, rhs)
      case t.Modulo(lhs, rhs) =>
        mkBin(rem(Unsigned), lhs, rhs)
      case t.UMinus(e) =>
        e.getType match {
          case t.RealType() => Unary(neg, transform(e))
          case tpe =>
            Binary(sub, zero(transform(tpe)), transform(e))
        }
      case t.LessThan(lhs, rhs) =>
        mkBin(typeToOp(lhs, lt(_), lt), lhs, rhs)
      case t.GreaterThan(lhs, rhs) =>
        mkBin(typeToOp(lhs, gt(_), gt), lhs, rhs)
      case t.LessEquals(lhs, rhs) =>
        mkBin(typeToOp(lhs, le(_), le), lhs, rhs)
      case t.GreaterEquals(lhs, rhs) =>
        mkBin(typeToOp(lhs, ge(_), ge), lhs, rhs)

      case t.BVNot(e) =>
        xor(zero(transform(e.getType)), transform(e))
      case t.BVAnd(lhs, rhs) =>
        mkBin(and, lhs, rhs)
      case t.BVOr(lhs, rhs) =>
        mkBin(or, lhs, rhs)
      case t.BVXor(lhs, rhs) =>
        mkBin(xor, lhs, rhs)
      case t.BVShiftLeft(lhs, rhs) =>
        mkBin(shl, lhs, rhs)
      case t.BVAShiftRight(lhs, rhs) =>
        mkBin(shr(Signed), lhs, rhs)
      case t.BVLShiftRight(lhs, rhs) =>
        mkBin(shr(Unsigned), lhs, rhs)
      case t.BVNarrowingCast(expr, newType) =>
        Wrap(transform(newType), transform(expr))
      case t.BVWideningCast(expr, newType) =>
        Extend(transform(newType), typeToSign(expr.getType), transform(expr))

      case t.And(exprs) =>
        exprs map transform reduceRight[Expr] { case (e1, e2) =>
          If(freshLabel("label"), e1, e2, I32Const(0))
        }
      case t.Or(exprs) =>
        exprs map transform reduceRight[Expr] { case (e1, e2) =>
          If(freshLabel("label"), e1, I32Const(1), e2)
        }
      case t.Not(expr) =>
        sub(I32Const(1), transform(expr))
    }
  }

  /** Transform a stainless type to a wasm type */
  def transform(tpe: t.Type)(implicit s: t.Symbols): Type = tpe match {
    case t.UnitType() => void
    case t.BooleanType() | t.CharType() => i32
    case t.IntegerType() => i64
    case t.RealType() => f64
    case t.BVType(_, size) => if (size > 32) i64 else i32
    case t.FunctionType(_, _) => i32
    case t.ArrayType(_) | t.RecordType(_) | t.StringType() =>
      sys.error("Reference types are left abstract " +
        "and have to be implemented in a subclass of wasm CodeGeneration")
  }

}
