/* Copyright 2009-2026 EPFL, Lausanne */

// Generated from semantics.md by inox.semantics.Codegen. Do not edit: change semantics.md
// and regenerate (see proofs/README.md).

package stainless.semantics.generated

import scala.language.unsafeNulls

object Semantics {
  type Id = inox.Identifier

  /** The euclidean quotient and remainder, as `div` and `mod` in the semantics; 0 and `a` for a
    * zero `b`, where the semantics leaves them unused. */
  def ediv(a: BigInt, b: BigInt): BigInt = if (b == 0) BigInt(0) else (a - emod(a, b)) / b
  def emod(a: BigInt, b: BigInt): BigInt = if (b == 0) a else a.mod(b.abs)

  sealed abstract class List[+T]
  final case class Nil() extends List[Nothing]
  final case class Cons[+T](head: T, tail: List[T]) extends List[T]

  sealed abstract class Option[+T]
  final case class None() extends Option[Nothing]
  final case class Some[+T](value: T) extends Option[T]

  sealed abstract class Result[+T]
  final case class Ok[+T](value: T) extends Result[T]
  final case class Stuck() extends Result[Nothing]
  final case class OutOfFuel() extends Result[Nothing]

  sealed abstract class Value
  final case class IntV(value: BigInt) extends Value
  final case class BoolV(value: Boolean) extends Value
  final case class UnitV() extends Value
  final case class CharV(code: BigInt) extends Value
  final case class RealV(num: BigInt, den: BigInt) extends Value
  final case class StringV(chars: List[BigInt]) extends Value
  final case class BVV(signed: Boolean, width: BigInt, bits: BigInt) extends Value
  final case class FPV(exponent: BigInt, significand: BigInt, bits: BigInt) extends Value
  final case class RoundingModeV(mode: RoundingMode) extends Value
  final case class TupleV(elems: List[Value]) extends Value
  final case class ClosureV(params: List[Param], body: Expr, env: Env) extends Value
  final case class SetV(elems: List[Value]) extends Value
  final case class BagV(entries: List[BagEntry]) extends Value
  final case class MapV(entries: List[MapEntry], default: Value) extends Value
  final case class ADTV(ctor: Id, args: List[Value]) extends Value
  final case class ArrayV(elems: List[Value]) extends Value

  final case class BagEntry(elem: Value, count: BigInt)

  final case class MapEntry(key: Value, value: Value)

  sealed abstract class Type
  final case class IntegerType() extends Type
  final case class BooleanType() extends Type
  final case class UnitType() extends Type
  final case class CharType() extends Type
  final case class RealType() extends Type
  final case class StringType() extends Type
  final case class BVType(signed: Boolean, width: BigInt) extends Type
  final case class FPType(exponent: BigInt, significand: BigInt) extends Type
  final case class RoundingModeType() extends Type
  final case class TypeParameter(id: Id) extends Type
  final case class TupleType(elems: List[Type]) extends Type
  final case class SetType(elem: Type) extends Type
  final case class BagType(elem: Type) extends Type
  final case class MapType(from: Type, to: Type) extends Type
  final case class FunctionType(from: List[Type], to: Type) extends Type
  final case class ADTType(sort: Id, args: List[Type]) extends Type
  final case class RefinementType(id: Id, base: Type, prop: Expr) extends Type
  final case class PropType() extends Type
  final case class PiType(params: List[Param], to: Type) extends Type
  final case class SigmaType(params: List[Param], to: Type) extends Type
  final case class ArrayType(base: Type) extends Type

  final case class Param(id: Id, tpe: Type)

  sealed abstract class Expr
  final case class Assume(pred: Expr, body: Expr) extends Expr
  final case class Variable(id: Id) extends Expr
  final case class Let(id: Id, value: Expr, body: Expr) extends Expr
  final case class Application(callee: Expr, args: List[Expr]) extends Expr
  final case class Lambda(params: List[Param], body: Expr) extends Expr
  final case class Forall(params: List[Param], body: Expr) extends Expr
  final case class UninterpretedCall(id: Id, tps: List[Type], args: List[Expr]) extends Expr
  final case class Error() extends Expr
  final case class FunctionInvocation(id: Id, tps: List[Type], args: List[Expr]) extends Expr
  final case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr
  final case class CharLiteral(code: BigInt) extends Expr
  final case class BVLiteral(signed: Boolean, width: BigInt, bits: BigInt) extends Expr
  final case class IntegerLiteral(value: BigInt) extends Expr
  final case class FractionLiteral(num: BigInt, den: BigInt) extends Expr
  final case class FPLiteral(exponent: BigInt, significand: BigInt, bits: BigInt) extends Expr
  final case class BooleanLiteral(value: Boolean) extends Expr
  final case class StringLiteral(chars: List[BigInt]) extends Expr
  final case class UnitLiteral() extends Expr
  final case class RoundNearestTiesToEven() extends Expr
  final case class RoundNearestTiesToAway() extends Expr
  final case class RoundTowardPositive() extends Expr
  final case class RoundTowardNegative() extends Expr
  final case class RoundTowardZero() extends Expr
  final case class ADT(id: Id, tps: List[Type], args: List[Expr]) extends Expr
  final case class IsConstructor(expr: Expr, id: Id) extends Expr
  final case class ADTSelector(adt: Expr, selector: Id) extends Expr
  final case class Equals(lhs: Expr, rhs: Expr) extends Expr
  final case class And(exprs: List[Expr]) extends Expr
  final case class Or(exprs: List[Expr]) extends Expr
  final case class Implies(lhs: Expr, rhs: Expr) extends Expr
  final case class Not(expr: Expr) extends Expr
  final case class StringConcat(lhs: Expr, rhs: Expr) extends Expr
  final case class SubString(expr: Expr, start: Expr, end: Expr) extends Expr
  final case class StringLength(expr: Expr) extends Expr
  final case class Plus(lhs: Expr, rhs: Expr) extends Expr
  final case class Minus(lhs: Expr, rhs: Expr) extends Expr
  final case class UMinus(expr: Expr) extends Expr
  final case class Times(lhs: Expr, rhs: Expr) extends Expr
  final case class Division(lhs: Expr, rhs: Expr) extends Expr
  final case class Remainder(lhs: Expr, rhs: Expr) extends Expr
  final case class Modulo(lhs: Expr, rhs: Expr) extends Expr
  final case class LessThan(lhs: Expr, rhs: Expr) extends Expr
  final case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr
  final case class LessEquals(lhs: Expr, rhs: Expr) extends Expr
  final case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr
  final case class BVNot(expr: Expr) extends Expr
  final case class BVAnd(lhs: Expr, rhs: Expr) extends Expr
  final case class BVOr(lhs: Expr, rhs: Expr) extends Expr
  final case class BVXor(lhs: Expr, rhs: Expr) extends Expr
  final case class BVShiftLeft(lhs: Expr, rhs: Expr) extends Expr
  final case class BVAShiftRight(lhs: Expr, rhs: Expr) extends Expr
  final case class BVLShiftRight(lhs: Expr, rhs: Expr) extends Expr
  final case class BVNarrowingCast(expr: Expr, width: BigInt) extends Expr
  final case class BVWideningCast(expr: Expr, width: BigInt) extends Expr
  final case class BVUnsignedToSigned(expr: Expr) extends Expr
  final case class BVSignedToUnsigned(expr: Expr) extends Expr
  final case class BVToInt(expr: Expr) extends Expr
  final case class IntToBV(width: BigInt, signed: Boolean, expr: Expr) extends Expr
  final case class FPEquals(lhs: Expr, rhs: Expr) extends Expr
  final case class FPAdd(rm: Expr, lhs: Expr, rhs: Expr) extends Expr
  final case class FPSub(rm: Expr, lhs: Expr, rhs: Expr) extends Expr
  final case class FPUMinus(expr: Expr) extends Expr
  final case class FPFMA(rm: Expr, e1: Expr, e2: Expr, e3: Expr) extends Expr
  final case class FPMul(rm: Expr, lhs: Expr, rhs: Expr) extends Expr
  final case class FPDiv(rm: Expr, lhs: Expr, rhs: Expr) extends Expr
  final case class FPAbs(expr: Expr) extends Expr
  final case class FPMax(lhs: Expr, rhs: Expr) extends Expr
  final case class FPMin(lhs: Expr, rhs: Expr) extends Expr
  final case class FPRound(rm: Expr, expr: Expr) extends Expr
  final case class Sqrt(rm: Expr, expr: Expr) extends Expr
  final case class FPCast(exponent: BigInt, significand: BigInt, rm: Expr, expr: Expr) extends Expr
  final case class FPFromBinary(exponent: BigInt, significand: BigInt, expr: Expr) extends Expr
  final case class FPToBV(width: BigInt, signed: Boolean, rm: Expr, expr: Expr) extends Expr
  final case class FPToReal(expr: Expr) extends Expr
  final case class FPLessThan(lhs: Expr, rhs: Expr) extends Expr
  final case class FPGreaterThan(lhs: Expr, rhs: Expr) extends Expr
  final case class FPLessEquals(lhs: Expr, rhs: Expr) extends Expr
  final case class FPGreaterEquals(lhs: Expr, rhs: Expr) extends Expr
  final case class FPIsZero(expr: Expr) extends Expr
  final case class FPIsInfinite(expr: Expr) extends Expr
  final case class FPIsNaN(expr: Expr) extends Expr
  final case class FPIsNegative(expr: Expr) extends Expr
  final case class FPIsPositive(expr: Expr) extends Expr
  final case class FPIsNormal(expr: Expr) extends Expr
  final case class FPIsSubnormal(expr: Expr) extends Expr
  final case class Tuple(exprs: List[Expr]) extends Expr
  final case class TupleSelect(tuple: Expr, index: BigInt) extends Expr
  final case class FiniteSet(elems: List[Expr]) extends Expr
  final case class SetAdd(set: Expr, elem: Expr) extends Expr
  final case class ElementOfSet(elem: Expr, set: Expr) extends Expr
  final case class SubsetOf(lhs: Expr, rhs: Expr) extends Expr
  final case class SetIntersection(lhs: Expr, rhs: Expr) extends Expr
  final case class SetUnion(lhs: Expr, rhs: Expr) extends Expr
  final case class SetDifference(lhs: Expr, rhs: Expr) extends Expr
  final case class FiniteBag(elems: List[ExprPair]) extends Expr
  final case class BagAdd(bag: Expr, elem: Expr) extends Expr
  final case class MultiplicityInBag(elem: Expr, bag: Expr) extends Expr
  final case class BagIntersection(lhs: Expr, rhs: Expr) extends Expr
  final case class BagUnion(lhs: Expr, rhs: Expr) extends Expr
  final case class BagDifference(lhs: Expr, rhs: Expr) extends Expr
  final case class FiniteMap(pairs: List[ExprPair], default: Expr) extends Expr
  final case class MapApply(map: Expr, key: Expr) extends Expr
  final case class MapUpdated(map: Expr, key: Expr, value: Expr) extends Expr
  final case class MapMerge(mask: Expr, map1: Expr, map2: Expr) extends Expr
  final case class NoTree() extends Expr
  final case class Choose(res: Id, tps: List[Type], tpe: Type, pred: Expr) extends Expr
  final case class Require(pred: Expr, body: Expr) extends Expr
  final case class Annotated(body: Expr) extends Expr
  final case class Ensuring(body: Expr, res: Id, post: Expr) extends Expr
  final case class Assert(pred: Expr, body: Expr) extends Expr
  final case class MatchExpr(scrutinee: Expr, cases: List[MatchCase]) extends Expr
  final case class Passes(in: Expr, out: Expr, cases: List[MatchCase]) extends Expr
  final case class JVMDivision(lhs: Expr, rhs: Expr) extends Expr
  final case class JVMRemainder(lhs: Expr, rhs: Expr) extends Expr
  final case class JVMShiftLeft(lhs: Expr, rhs: Expr) extends Expr
  final case class JVMAShiftRight(lhs: Expr, rhs: Expr) extends Expr
  final case class JVMLShiftRight(lhs: Expr, rhs: Expr) extends Expr
  final case class FiniteArray(elems: List[Expr]) extends Expr
  final case class LargeArray(elems: List[ArrayEntry], default: Expr, size: Expr) extends Expr
  final case class ArraySelect(array: Expr, index: Expr) extends Expr
  final case class ArrayUpdated(array: Expr, index: Expr, value: Expr) extends Expr
  final case class ArrayLength(array: Expr) extends Expr
  final case class Decreases(body: Expr) extends Expr
  final case class Max(exprs: List[Expr]) extends Expr
  final case class SizedADT(id: Id, tps: List[Type], args: List[Expr], size: Expr) extends Expr

  final case class ExprPair(fst: Expr, snd: Expr)

  final case class FunDef(id: Id, tparams: List[Id], params: List[Id], body: Expr)

  final case class Constructor(id: Id, sort: Id, fields: List[Param])

  final case class Sort(id: Id, tparams: List[Id], invariant: Option[Id])

  final case class Interpretation(id: Id, tps: List[Type], params: List[Id], body: Expr)

  sealed abstract class FunctionEquality
  final case class NoFunctionEquality() extends FunctionEquality
  final case class ExtensionalEquality() extends FunctionEquality

  final case class Program(functions: List[FunDef], constructors: List[Constructor], sorts: List[Sort], interpretations: List[Interpretation], equality: FunctionEquality)

  final case class Binding(id: Id, value: Value)

  final case class TypeBinding(id: Id, tpe: Type, env: List[TypeBinding])

  final case class Env(types: List[TypeBinding], vars: List[Binding])

  sealed abstract class BitOp
  final case class AndOp() extends BitOp
  final case class OrOp() extends BitOp
  final case class XorOp() extends BitOp
  final case class ShiftLeftOp() extends BitOp
  final case class AShiftRightOp() extends BitOp
  final case class LShiftRightOp() extends BitOp

  sealed abstract class RoundingMode
  final case class RNE() extends RoundingMode
  final case class RNA() extends RoundingMode
  final case class RTP() extends RoundingMode
  final case class RTN() extends RoundingMode
  final case class RTZ() extends RoundingMode

  final case class Rat(num: BigInt, den: BigInt)

  sealed abstract class FPOp
  final case class FPAddOp() extends FPOp
  final case class FPSubOp() extends FPOp
  final case class FPMulOp() extends FPOp
  final case class FPDivOp() extends FPOp
  final case class FPMinOp() extends FPOp
  final case class FPMaxOp() extends FPOp

  sealed abstract class FPRel
  final case class FPEqRel() extends FPRel
  final case class FPLtRel() extends FPRel
  final case class FPLeRel() extends FPRel

  sealed abstract class FPClass
  final case class ZeroClass() extends FPClass
  final case class InfiniteClass() extends FPClass
  final case class NaNClass() extends FPClass
  final case class NegativeClass() extends FPClass
  final case class PositiveClass() extends FPClass
  final case class NormalClass() extends FPClass
  final case class SubnormalClass() extends FPClass

  sealed abstract class BagOp
  final case class IntersectionOp() extends BagOp
  final case class UnionOp() extends BagOp
  final case class DifferenceOp() extends BagOp

  final case class ArrayEntry(index: BigInt, value: Expr)

  final case class MatchCase(pattern: Pattern, guard: Option[Expr], rhs: Expr)

  sealed abstract class Pattern
  final case class WildcardPattern(binder: Option[Id]) extends Pattern
  final case class ADTPattern(binder: Option[Id], id: Id, subs: List[Pattern]) extends Pattern
  final case class TuplePattern(binder: Option[Id], subs: List[Pattern]) extends Pattern
  final case class LiteralPattern(binder: Option[Id], lit: Expr) extends Pattern
  final case class AlternativePattern(binder: Option[Id], subs: List[Pattern]) extends Pattern
  final case class RefinementPattern(underlying: Pattern, param: Id, pred: Expr) extends Pattern
  final case class UnapplyPattern(binder: Option[Id], recs: List[Expr], id: Id, tps: List[Type], is_empty: Id, is_empty_tps: List[Type], get: Id, get_tps: List[Type], subs: List[Pattern]) extends Pattern

  final case class ArrayEntryValue(index: BigInt, value: Value)

  /** The functions of the semantics. Those that quantify over values are abstract, and a
    * subclass gives them. */
  abstract class Evaluator {
    def lookup_var(vars: List[Binding], x: Id): Result[Value] =
      ((vars) match {
        case Nil() => Stuck()
        case Cons(Binding(y, v), rest) => (if ((x == y)) {
            Ok(v)
          } else {
            lookup_var(rest, x)
          })
      })

    def lookup_type(types: List[TypeBinding], x: Id): Option[TypeBinding] =
      ((types) match {
        case Nil() => None()
        case Cons(b, rest) => ((b) match {
            case TypeBinding(y, _, _) => (if ((x == y)) {
                Some(b)
              } else {
                lookup_type(rest, x)
              })
          })
      })

    def bind_types(ids: List[Id], tps: List[Type], env: List[TypeBinding]): List[TypeBinding] =
      ((ids) match {
        case Nil() => Nil()
        case Cons(x, xs) => ((tps) match {
            case Nil() => Nil()
            case Cons(t, ts) => Cons(TypeBinding(x, t, env), bind_types(xs, ts, env))
          })
      })

    def env_types(env: Env): List[TypeBinding] =
      ((env) match {
        case Env(tys, _) => tys
      })

    def env_vars(env: Env): List[Binding] =
      ((env) match {
        case Env(_, vars) => vars
      })

    def env_bind(env: Env, x: Id, v: Value): Env =
      ((env) match {
        case Env(tys, vars) => Env(tys, Cons(Binding(x, v), vars))
      })

    def param_ids(ps: List[Param]): List[Id] =
      ((ps) match {
        case Nil() => Nil()
        case Cons(Param(x, _), rest) => Cons(x, param_ids(rest))
      })

    def bind_all(ids: List[Id], vs: List[Value]): Result[List[Binding]] =
      ((ids) match {
        case Nil() => ((vs) match {
            case Nil() => Ok(Nil())
            case _ => Stuck()
          })
        case Cons(x, xs) => ((vs) match {
            case Nil() => Stuck()
            case Cons(v, rest) => bind_all(xs, rest) match {
                case Ok(bs) => Ok(Cons(Binding(x, v), bs))
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
          })
      })

    def lookup_fun(fs: List[FunDef], f: Id): Result[FunDef] =
      ((fs) match {
        case Nil() => Stuck()
        case Cons(fd, rest) => ((fd) match {
            case FunDef(g, _, _, _) => (if ((f == g)) {
                Ok(fd)
              } else {
                lookup_fun(rest, f)
              })
          })
      })

    def lookup_ctor(cs: List[Constructor], c: Id): Result[Constructor] =
      ((cs) match {
        case Nil() => Stuck()
        case Cons(k, rest) => ((k) match {
            case Constructor(d, _, _) => (if ((c == d)) {
                Ok(k)
              } else {
                lookup_ctor(rest, c)
              })
          })
      })

    def lookup_sort(ss: List[Sort], s: Id): Result[Sort] =
      ((ss) match {
        case Nil() => Stuck()
        case Cons(srt, rest) => ((srt) match {
            case Sort(t, _, _) => (if ((s == t)) {
                Ok(srt)
              } else {
                lookup_sort(rest, s)
              })
          })
      })

    def select_field(fields: List[Param], args: List[Value], sel: Id): Result[Value] =
      ((fields) match {
        case Nil() => Stuck()
        case Cons(Param(f, _), fs) => ((args) match {
            case Nil() => Stuck()
            case Cons(v, vs) => (if ((f == sel)) {
                Ok(v)
              } else {
                select_field(fs, vs, sel)
              })
          })
      })

    def call(v_P: Program, fuel: BigInt, f: Id, tps: List[Type], tenv: List[TypeBinding], vs: List[Value]): Result[Value] =
      (if ((fuel <= BigInt(0))) {
        OutOfFuel()
      } else {
        ((v_P) match {
          case Program(fs, _, _, _, _) => lookup_fun(fs, f) match {
              case Ok(fd) => ((fd) match {
                case FunDef(_, tparams, params, body) => bind_all(params, vs) match {
                    case Ok(bs) => eval(v_P, (fuel - BigInt(1)), Env(bind_types(tparams, tps, tenv), bs), body)
                    case Stuck() => Stuck()
                    case OutOfFuel() => OutOfFuel()
                  }
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
        })
      })

    def eval(v_P: Program, fuel: BigInt, env: Env, e: Expr): Result[Value] = e match {
      case Assume(pred, body) =>
        eval_bool(v_P, fuel, env, pred) match {
          case Ok(b) => (if (b) {
            eval(v_P, fuel, env, body)
          } else {
            Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Variable(x) =>
        lookup_var(env_vars(env), x)
      case Let(x, value, body) =>
        eval(v_P, fuel, env, value) match {
          case Ok(v) => eval(v_P, fuel, env_bind(env, x, v), body)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Application(callee, args) =>
        eval(v_P, fuel, env, callee) match {
          case Ok(f) => eval_list(v_P, fuel, env, args) match {
            case Ok(vs) => apply(v_P, fuel, f, vs)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Lambda(params, body) =>
        Ok(ClosureV(params, body, env))
      case Forall(params, body) =>
        forall_result(v_P, fuel, env, params, body)
      case UninterpretedCall(f, tps, args) =>
        eval_list(v_P, fuel, env, args) match {
          case Ok(vs) => (if ((fuel <= BigInt(0))) {
            OutOfFuel()
          } else {
            ((v_P) match {
              case Program(_, _, _, is, _) => lookup_interpretation(is, f, resolve_all(env_types(env), tps)) match {
                  case Ok(i) => ((i) match {
                    case Interpretation(_, _, params, body) => bind_all(params, vs) match {
                        case Ok(bs) => eval(v_P, (fuel - BigInt(1)), Env(Nil(), bs), body)
                        case Stuck() => Stuck()
                        case OutOfFuel() => OutOfFuel()
                      }
                  })
                  case Stuck() => Stuck()
                  case OutOfFuel() => OutOfFuel()
                }
            })
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Error() =>
        Stuck()
      case FunctionInvocation(f, tps, args) =>
        eval_list(v_P, fuel, env, args) match {
          case Ok(vs) => call(v_P, fuel, f, tps, env_types(env), vs)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case IfExpr(cond, thenn, elze) =>
        eval_bool(v_P, fuel, env, cond) match {
          case Ok(b) => (if (b) {
            eval(v_P, fuel, env, thenn)
          } else {
            eval(v_P, fuel, env, elze)
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case CharLiteral(c) =>
        Ok(CharV(c))
      case BVLiteral(s, w, x) =>
        Ok(BVV(s, w, x))
      case IntegerLiteral(i) =>
        Ok(IntV(i))
      case FractionLiteral(n, d) =>
        real(n, d)
      case FPLiteral(e, s, x) =>
        Ok(FPV(e, s, fp_canonical(e, s, x)))
      case BooleanLiteral(b) =>
        Ok(BoolV(b))
      case StringLiteral(cs) =>
        Ok(StringV(cs))
      case UnitLiteral() =>
        Ok(UnitV())
      case RoundNearestTiesToEven() =>
        Ok(RoundingModeV(RNE()))
      case RoundNearestTiesToAway() =>
        Ok(RoundingModeV(RNA()))
      case RoundTowardPositive() =>
        Ok(RoundingModeV(RTP()))
      case RoundTowardNegative() =>
        Ok(RoundingModeV(RTN()))
      case RoundTowardZero() =>
        Ok(RoundingModeV(RTZ()))
      case ADT(c, tps, args) =>
        eval_list(v_P, fuel, env, args) match {
          case Ok(vs) => construct(v_P, fuel, env, c, tps, vs)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case IsConstructor(adt, c) =>
        eval(v_P, fuel, env, adt) match {
          case Ok(v) => ((v) match {
            case ADTV(d, _) => Ok(BoolV((c == d)))
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case ADTSelector(adt, sel) =>
        eval(v_P, fuel, env, adt) match {
          case Ok(v) => ((v) match {
            case ADTV(c, vs) => ((v_P) match {
                case Program(_, cs, _, _, _) => lookup_ctor(cs, c) match {
                    case Ok(k) => ((k) match {
                      case Constructor(_, _, fields) => select_field(fields, vs, sel)
                    })
                    case Stuck() => Stuck()
                    case OutOfFuel() => OutOfFuel()
                  }
              })
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Equals(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => value_eq(v_P, a, b) match {
              case Ok(same) => Ok(BoolV(same))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case And(es) =>
        eval_and(v_P, fuel, env, es)
      case Or(es) =>
        eval_or(v_P, fuel, env, es)
      case Implies(lhs, rhs) =>
        eval_bool(v_P, fuel, env, lhs) match {
          case Ok(a) => (if (a) {
            eval_bool(v_P, fuel, env, rhs) match {
              case Ok(b) => Ok(BoolV(b))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          } else {
            Ok(BoolV(true))
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Not(expr) =>
        eval_bool(v_P, fuel, env, expr) match {
          case Ok(a) => Ok(BoolV(!(a)))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case StringConcat(lhs, rhs) =>
        eval_string(v_P, fuel, env, lhs) match {
          case Ok(a) => eval_string(v_P, fuel, env, rhs) match {
            case Ok(b) => Ok(StringV(append_chars(a, b)))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case SubString(expr, start, end) =>
        eval_string(v_P, fuel, env, expr) match {
          case Ok(cs) => eval_int(v_P, fuel, env, start) match {
            case Ok(b) => eval_int(v_P, fuel, env, end) match {
              case Ok(c) => (if (((b < BigInt(0)) || (c <= b))) {
                Ok(StringV(Nil()))
              } else {
                Ok(StringV(take((c - b), drop(b, cs))))
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case StringLength(expr) =>
        eval_string(v_P, fuel, env, expr) match {
          case Ok(cs) => Ok(IntV(length(cs)))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Plus(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => arith_plus(a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Minus(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => arith_minus(a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case UMinus(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => arith_neg(a)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Times(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => arith_times(a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Division(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => arith_div(a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Remainder(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => arith_rem(a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Modulo(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => arith_mod(a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case LessThan(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => arith_lt(a, b) match {
              case Ok(r) => Ok(BoolV(r))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case GreaterThan(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => arith_lt(b, a) match {
              case Ok(r) => Ok(BoolV(r))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case LessEquals(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => arith_le(a, b) match {
              case Ok(r) => Ok(BoolV(r))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case GreaterEquals(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => arith_le(b, a) match {
              case Ok(r) => Ok(BoolV(r))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVNot(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => ((a) match {
            case BVV(s, w, x) => Ok(BVV(s, w, ((pow2(w) - BigInt(1)) - x)))
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVAnd(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => bv_binary(AndOp(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVOr(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => bv_binary(OrOp(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVXor(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => bv_binary(XorOp(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVShiftLeft(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => bv_binary(ShiftLeftOp(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVAShiftRight(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => bv_binary(AShiftRightOp(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVLShiftRight(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => bv_binary(LShiftRightOp(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVNarrowingCast(expr, w) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => bv_cast(a, w)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVWideningCast(expr, w) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => bv_cast(a, w)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVUnsignedToSigned(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => ((a) match {
            case BVV(false, w, x) => Ok(BVV(true, w, x))
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVSignedToUnsigned(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => ((a) match {
            case BVV(true, w, x) => Ok(BVV(false, w, x))
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BVToInt(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => ((a) match {
            case BVV(s, w, x) => Ok(IntV(bv_int(s, w, x)))
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case IntToBV(w, s, expr) =>
        eval_int(v_P, fuel, env, expr) match {
          case Ok(i) => Ok(bv(s, w, i))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPEquals(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => fp_rel(FPEqRel(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPAdd(rm, lhs, rhs) =>
        eval_rm(v_P, fuel, env, rm) match {
          case Ok(m) => eval(v_P, fuel, env, lhs) match {
            case Ok(a) => eval(v_P, fuel, env, rhs) match {
              case Ok(b) => fp_binary(FPAddOp(), m, a, b)
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPSub(rm, lhs, rhs) =>
        eval_rm(v_P, fuel, env, rm) match {
          case Ok(m) => eval(v_P, fuel, env, lhs) match {
            case Ok(a) => eval(v_P, fuel, env, rhs) match {
              case Ok(b) => fp_binary(FPSubOp(), m, a, b)
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPUMinus(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => ((a) match {
            case FPV(e, s, x) => Ok(FPV(e, s, fp_neg(e, s, x)))
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPFMA(rm, e1, e2, e3) =>
        eval_rm(v_P, fuel, env, rm) match {
          case Ok(m) => eval(v_P, fuel, env, e1) match {
            case Ok(a) => eval(v_P, fuel, env, e2) match {
              case Ok(b) => eval(v_P, fuel, env, e3) match {
                case Ok(c) => ((a) match {
                  case FPV(e, s, x) => ((b) match {
                      case FPV(e2, s2, y) => ((c) match {
                          case FPV(e3, s3, z) => (if ((((e == e2) && (s == s2)) && ((e == e3) && (s == s3)))) {
                              Ok(FPV(e, s, fp_fma(m, e, s, x, y, z)))
                            } else {
                              Stuck()
                            })
                          case _ => Stuck()
                        })
                      case _ => Stuck()
                    })
                  case _ => Stuck()
                })
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPMul(rm, lhs, rhs) =>
        eval_rm(v_P, fuel, env, rm) match {
          case Ok(m) => eval(v_P, fuel, env, lhs) match {
            case Ok(a) => eval(v_P, fuel, env, rhs) match {
              case Ok(b) => fp_binary(FPMulOp(), m, a, b)
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPDiv(rm, lhs, rhs) =>
        eval_rm(v_P, fuel, env, rm) match {
          case Ok(m) => eval(v_P, fuel, env, lhs) match {
            case Ok(a) => eval(v_P, fuel, env, rhs) match {
              case Ok(b) => fp_binary(FPDivOp(), m, a, b)
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPAbs(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => ((a) match {
            case FPV(e, s, x) => Ok(FPV(e, s, fp_abs(e, s, x)))
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPMax(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => fp_binary(FPMaxOp(), RNE(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPMin(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => fp_binary(FPMinOp(), RNE(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPRound(rm, expr) =>
        eval_rm(v_P, fuel, env, rm) match {
          case Ok(m) => eval(v_P, fuel, env, expr) match {
            case Ok(a) => ((a) match {
              case FPV(e, s, x) => Ok(FPV(e, s, fp_round_integral(m, e, s, x)))
              case _ => Stuck()
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Sqrt(rm, expr) =>
        eval_rm(v_P, fuel, env, rm) match {
          case Ok(m) => eval(v_P, fuel, env, expr) match {
            case Ok(a) => ((a) match {
              case FPV(e, s, x) => Ok(FPV(e, s, fp_sqrt(m, e, s, x)))
              case _ => Stuck()
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPCast(e, s, rm, expr) =>
        eval_rm(v_P, fuel, env, rm) match {
          case Ok(m) => eval(v_P, fuel, env, expr) match {
            case Ok(a) => fp_cast(m, e, s, a) match {
              case Ok(x) => Ok(FPV(e, s, x))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPFromBinary(e, s, expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => ((a) match {
            case BVV(_, w, x) => (if ((w == (e + s))) {
                Ok(FPV(e, s, fp_canonical(e, s, x)))
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPToBV(w, sg, rm, expr) =>
        eval_rm(v_P, fuel, env, rm) match {
          case Ok(m) => eval(v_P, fuel, env, expr) match {
            case Ok(a) => ((a) match {
              case FPV(e, s, x) => {
                  val lo = (if (sg) {
                    (BigInt(0) - pow2((w - BigInt(1))))
                  } else {
                    BigInt(0)
                  })
                  val hi = (if (sg) {
                    (pow2((w - BigInt(1))) - BigInt(1))
                  } else {
                    (pow2(w) - BigInt(1))
                  })
                  Ok(bv(sg, w, fp_to_int(m, e, s, x, lo, hi)))
                }
              case _ => Stuck()
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPToReal(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => ((a) match {
            case FPV(e, s, x) => (if ((fp_nan(e, s, x) || fp_inf(e, s, x))) {
                Stuck()
              } else {
                ((fp_rat(e, s, x)) match {
                  case Rat(n, d) => real(n, d)
                })
              })
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPLessThan(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => fp_rel(FPLtRel(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPGreaterThan(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => fp_rel(FPLtRel(), b, a)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPLessEquals(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => fp_rel(FPLeRel(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPGreaterEquals(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => fp_rel(FPLeRel(), b, a)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPIsZero(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => fp_class(ZeroClass(), a)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPIsInfinite(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => fp_class(InfiniteClass(), a)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPIsNaN(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => fp_class(NaNClass(), a)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPIsNegative(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => fp_class(NegativeClass(), a)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPIsPositive(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => fp_class(PositiveClass(), a)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPIsNormal(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => fp_class(NormalClass(), a)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FPIsSubnormal(expr) =>
        eval(v_P, fuel, env, expr) match {
          case Ok(a) => fp_class(SubnormalClass(), a)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Tuple(es) =>
        eval_list(v_P, fuel, env, es) match {
          case Ok(vs) => Ok(TupleV(vs))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case TupleSelect(tuple, i) =>
        eval(v_P, fuel, env, tuple) match {
          case Ok(t) => ((t) match {
            case TupleV(vs) => nth(vs, i)
            case _ => Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FiniteSet(es) =>
        eval_list(v_P, fuel, env, es) match {
          case Ok(vs) => set_insert_all(v_P, Nil(), vs) match {
            case Ok(xs) => Ok(SetV(xs))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case SetAdd(set, elem) =>
        eval_set(v_P, fuel, env, set) match {
          case Ok(xs) => eval(v_P, fuel, env, elem) match {
            case Ok(v) => set_insert(v_P, xs, v) match {
              case Ok(ys) => Ok(SetV(ys))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case ElementOfSet(elem, set) =>
        eval(v_P, fuel, env, elem) match {
          case Ok(v) => eval_set(v_P, fuel, env, set) match {
            case Ok(xs) => set_contains(v_P, xs, v) match {
              case Ok(in) => Ok(BoolV(in))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case SubsetOf(lhs, rhs) =>
        eval_set(v_P, fuel, env, lhs) match {
          case Ok(xs) => eval_set(v_P, fuel, env, rhs) match {
            case Ok(ys) => subset(v_P, xs, ys) match {
              case Ok(sub) => Ok(BoolV(sub))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case SetIntersection(lhs, rhs) =>
        eval_set(v_P, fuel, env, lhs) match {
          case Ok(xs) => eval_set(v_P, fuel, env, rhs) match {
            case Ok(ys) => set_filter(v_P, xs, ys, true) match {
              case Ok(zs) => Ok(SetV(zs))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case SetUnion(lhs, rhs) =>
        eval_set(v_P, fuel, env, lhs) match {
          case Ok(xs) => eval_set(v_P, fuel, env, rhs) match {
            case Ok(ys) => set_insert_all(v_P, xs, ys) match {
              case Ok(zs) => Ok(SetV(zs))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case SetDifference(lhs, rhs) =>
        eval_set(v_P, fuel, env, lhs) match {
          case Ok(xs) => eval_set(v_P, fuel, env, rhs) match {
            case Ok(ys) => set_filter(v_P, xs, ys, false) match {
              case Ok(zs) => Ok(SetV(zs))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FiniteBag(es) =>
        eval_bag_entries(v_P, fuel, env, Nil(), es) match {
          case Ok(xs) => Ok(BagV(xs))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BagAdd(bag, elem) =>
        eval_bag(v_P, fuel, env, bag) match {
          case Ok(xs) => eval(v_P, fuel, env, elem) match {
            case Ok(v) => bag_get(v_P, xs, v) match {
              case Ok(n) => bag_set(v_P, xs, v, (n + BigInt(1))) match {
                case Ok(ys) => Ok(BagV(ys))
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case MultiplicityInBag(elem, bag) =>
        eval(v_P, fuel, env, elem) match {
          case Ok(v) => eval_bag(v_P, fuel, env, bag) match {
            case Ok(xs) => bag_get(v_P, xs, v) match {
              case Ok(n) => Ok(IntV(n))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BagIntersection(lhs, rhs) =>
        eval_bag(v_P, fuel, env, lhs) match {
          case Ok(xs) => eval_bag(v_P, fuel, env, rhs) match {
            case Ok(ys) => bag_merge(v_P, IntersectionOp(), Nil(), xs, ys) match {
              case Ok(zs) => Ok(BagV(zs))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BagUnion(lhs, rhs) =>
        eval_bag(v_P, fuel, env, lhs) match {
          case Ok(xs) => eval_bag(v_P, fuel, env, rhs) match {
            case Ok(ys) => bag_add_all(v_P, xs, ys) match {
              case Ok(zs) => Ok(BagV(zs))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case BagDifference(lhs, rhs) =>
        eval_bag(v_P, fuel, env, lhs) match {
          case Ok(xs) => eval_bag(v_P, fuel, env, rhs) match {
            case Ok(ys) => bag_merge(v_P, DifferenceOp(), Nil(), xs, ys) match {
              case Ok(zs) => Ok(BagV(zs))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FiniteMap(pairs, default) =>
        eval_map_entries(v_P, fuel, env, Nil(), pairs) match {
          case Ok(xs) => eval(v_P, fuel, env, default) match {
            case Ok(d) => Ok(MapV(xs, d))
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case MapApply(map, key) =>
        eval(v_P, fuel, env, map) match {
          case Ok(m) => eval(v_P, fuel, env, key) match {
            case Ok(k) => ((m) match {
              case MapV(xs, d) => map_get(v_P, xs, k, d)
              case _ => Stuck()
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case MapUpdated(map, key, value) =>
        eval(v_P, fuel, env, map) match {
          case Ok(m) => eval(v_P, fuel, env, key) match {
            case Ok(k) => eval(v_P, fuel, env, value) match {
              case Ok(v) => ((m) match {
                case MapV(xs, d) => map_put(v_P, xs, k, v) match {
                    case Ok(ys) => Ok(MapV(ys, d))
                    case Stuck() => Stuck()
                    case OutOfFuel() => OutOfFuel()
                  }
                case _ => Stuck()
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case MapMerge(mask, map1, map2) =>
        eval_set(v_P, fuel, env, mask) match {
          case Ok(ks) => eval(v_P, fuel, env, map1) match {
            case Ok(m1) => eval(v_P, fuel, env, map2) match {
              case Ok(m2) => ((m1) match {
                case MapV(xs, d1) => ((m2) match {
                    case MapV(ys, d2) => map_without(v_P, ys, ks) match {
                        case Ok(rest) => map_take(v_P, rest, ks, xs, d1) match {
                          case Ok(zs) => Ok(MapV(zs, d2))
                          case Stuck() => Stuck()
                          case OutOfFuel() => OutOfFuel()
                        }
                        case Stuck() => Stuck()
                        case OutOfFuel() => OutOfFuel()
                      }
                    case _ => Stuck()
                  })
                case _ => Stuck()
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case NoTree() =>
        Stuck()
      case Choose(res, tps, tpe, pred) =>
        (if ((fuel <= BigInt(0))) {
          OutOfFuel()
        } else {
          ((v_P) match {
            case Program(_, _, _, is, _) => lookup_interpretation(is, res, resolve_all(env_types(env), tps)) match {
                case Ok(i) => ((i) match {
                  case Interpretation(_, _, params, body) => lookup_vars(env_vars(env), params) match {
                      case Ok(bs) => eval(v_P, (fuel - BigInt(1)), Env(Nil(), bs), body) match {
                        case Ok(v) => eval_bool(v_P, fuel, env_bind(env, res, v), pred) match {
                          case Ok(b) => (if ((b && has_type(v_P, env, v, tpe))) {
                            Ok(v)
                          } else {
                            Stuck()
                          })
                          case Stuck() => Stuck()
                          case OutOfFuel() => OutOfFuel()
                        }
                        case Stuck() => Stuck()
                        case OutOfFuel() => OutOfFuel()
                      }
                      case Stuck() => Stuck()
                      case OutOfFuel() => OutOfFuel()
                    }
                })
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
          })
        })
      case Require(pred, body) =>
        eval_bool(v_P, fuel, env, pred) match {
          case Ok(b) => (if (b) {
            eval(v_P, fuel, env, body)
          } else {
            Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Annotated(body) =>
        eval(v_P, fuel, env, body)
      case Ensuring(body, res, post) =>
        eval(v_P, fuel, env, body) match {
          case Ok(v) => eval_bool(v_P, fuel, env_bind(env, res, v), post) match {
            case Ok(b) => (if (b) {
              Ok(v)
            } else {
              Stuck()
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Assert(pred, body) =>
        eval_bool(v_P, fuel, env, pred) match {
          case Ok(b) => (if (b) {
            eval(v_P, fuel, env, body)
          } else {
            Stuck()
          })
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case MatchExpr(scrutinee, cases) =>
        eval(v_P, fuel, env, scrutinee) match {
          case Ok(v) => eval_cases(v_P, fuel, env, v, cases, Stuck())
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Passes(in, out, cases) =>
        eval(v_P, fuel, env, out) match {
          case Ok(o) => eval(v_P, fuel, env, in) match {
            case Ok(v) => eval_cases(v_P, fuel, env, v, cases, Ok(o)) match {
              case Ok(r) => value_eq(v_P, o, r) match {
                case Ok(same) => Ok(BoolV(same))
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case JVMDivision(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => (if (zero_divisor(b)) {
              Stuck()
            } else {
              ((a) match {
                case IntV(x) => ((b) match {
                    case IntV(y) => Ok(IntV(tdiv(x, y)))
                    case _ => Stuck()
                  })
                case _ => arith_div(a, b)
              })
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case JVMRemainder(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => (if (zero_divisor(b)) {
              Stuck()
            } else {
              ((a) match {
                case IntV(x) => ((b) match {
                    case IntV(y) => Ok(IntV(trem(x, y)))
                    case _ => Stuck()
                  })
                case _ => arith_rem(a, b)
              })
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case JVMShiftLeft(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => jvm_shift(ShiftLeftOp(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case JVMAShiftRight(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => jvm_shift(AShiftRightOp(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case JVMLShiftRight(lhs, rhs) =>
        eval(v_P, fuel, env, lhs) match {
          case Ok(a) => eval(v_P, fuel, env, rhs) match {
            case Ok(b) => jvm_shift(LShiftRightOp(), a, b)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case FiniteArray(elems) =>
        eval_list(v_P, fuel, env, elems) match {
          case Ok(vs) => Ok(ArrayV(vs))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case LargeArray(elems, default, size) =>
        eval_entries(v_P, fuel, env, elems) match {
          case Ok(es) => eval(v_P, fuel, env, default) match {
            case Ok(d) => eval_index(v_P, fuel, env, size) match {
              case Ok(n) => (if ((n < BigInt(0))) {
                Stuck()
              } else {
                Ok(ArrayV(array_fill(BigInt(0), n, d, es)))
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case ArraySelect(array, index) =>
        eval_array(v_P, fuel, env, array) match {
          case Ok(vs) => eval_index(v_P, fuel, env, index) match {
            case Ok(i) => array_get(vs, i)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case ArrayUpdated(array, index, value) =>
        eval_array(v_P, fuel, env, array) match {
          case Ok(vs) => eval_index(v_P, fuel, env, index) match {
            case Ok(i) => eval(v_P, fuel, env, value) match {
              case Ok(v) => array_set(vs, i, v) match {
                case Ok(ws) => Ok(ArrayV(ws))
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case ArrayLength(array) =>
        eval_array(v_P, fuel, env, array) match {
          case Ok(vs) => Ok(bv(true, BigInt(32), values_length(vs)))
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case Decreases(body) =>
        eval(v_P, fuel, env, body)
      case Max(exprs) =>
        eval_list(v_P, fuel, env, exprs) match {
          case Ok(vs) => int_max(vs)
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
      case SizedADT(c, tps, args, size) =>
        eval_list(v_P, fuel, env, args) match {
          case Ok(vs) => eval(v_P, fuel, env, size) match {
            case Ok(n) => construct(v_P, fuel, env, c, tps, vs)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
          case Stuck() => Stuck()
          case OutOfFuel() => OutOfFuel()
        }
    }

    def eval_list(v_P: Program, fuel: BigInt, env: Env, es: List[Expr]): Result[List[Value]] =
      ((es) match {
        case Nil() => Ok(Nil())
        case Cons(e, rest) => eval(v_P, fuel, env, e) match {
            case Ok(v) => eval_list(v_P, fuel, env, rest) match {
              case Ok(vs) => Ok(Cons(v, vs))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def eval_int(v_P: Program, fuel: BigInt, env: Env, e: Expr): Result[BigInt] =
      eval(v_P, fuel, env, e) match {
        case Ok(v) => ((v) match {
          case IntV(i) => Ok(i)
          case _ => Stuck()
        })
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def eval_bool(v_P: Program, fuel: BigInt, env: Env, e: Expr): Result[Boolean] =
      eval(v_P, fuel, env, e) match {
        case Ok(v) => ((v) match {
          case BoolV(b) => Ok(b)
          case _ => Stuck()
        })
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def construct(v_P: Program, fuel: BigInt, env: Env, c: Id, tps: List[Type], vs: List[Value]): Result[Value] =
      ((v_P) match {
        case Program(_, cs, ss, _, _) => lookup_ctor(cs, c) match {
            case Ok(k) => ((k) match {
              case Constructor(_, s, _) => lookup_sort(ss, s) match {
                  case Ok(srt) => ((srt) match {
                    case Sort(_, _, None()) => Ok(ADTV(c, vs))
                    case Sort(_, _, Some(inv)) => call(v_P, fuel, inv, tps, env_types(env), Cons(ADTV(c, vs), Nil())) match {
                        case Ok(holds) => ((holds) match {
                          case BoolV(true) => Ok(ADTV(c, vs))
                          case _ => Stuck()
                        })
                        case Stuck() => Stuck()
                        case OutOfFuel() => OutOfFuel()
                      }
                  })
                  case Stuck() => Stuck()
                  case OutOfFuel() => OutOfFuel()
                }
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def value_eq(v_P: Program, a: Value, b: Value): Result[Boolean] = a match {
      case IntV(_) =>
        Ok((a == b))
      case BoolV(_) =>
        Ok((a == b))
      case UnitV() =>
        Ok((a == b))
      case CharV(_) =>
        Ok((a == b))
      case RealV(_, _) =>
        Ok((a == b))
      case StringV(_) =>
        Ok((a == b))
      case BVV(_, _, _) =>
        Ok((a == b))
      case FPV(_, _, _) =>
        Ok((a == b))
      case RoundingModeV(_) =>
        Ok((a == b))
      case TupleV(xs) =>
        ((b) match {
          case TupleV(ys) => values_eq(v_P, xs, ys)
          case _ => Ok(false)
        })
      case ClosureV(_, _, _) =>
        ((v_P) match {
          case Program(_, _, _, _, eq) => ((eq) match {
              case NoFunctionEquality() => Stuck()
              case ExtensionalEquality() => Ok(closures_equal(v_P, a, b))
            })
        })
      case SetV(xs) =>
        ((b) match {
          case SetV(ys) => subset(v_P, xs, ys) match {
              case Ok(sub) => (if (sub) {
                subset(v_P, ys, xs)
              } else {
                Ok(false)
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          case _ => Ok(false)
        })
      case BagV(xs) =>
        ((b) match {
          case BagV(ys) => sub_bag(v_P, xs, ys) match {
              case Ok(sub) => (if (sub) {
                sub_bag(v_P, ys, xs)
              } else {
                Ok(false)
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          case _ => Ok(false)
        })
      case MapV(xs, d) =>
        ((b) match {
          case MapV(ys, e) => value_eq(v_P, d, e) match {
              case Ok(same) => (if (same) {
                same_entries(v_P, xs, xs, d, ys, e) match {
                  case Ok(l) => (if (l) {
                    same_entries(v_P, ys, xs, d, ys, e)
                  } else {
                    Ok(false)
                  })
                  case Stuck() => Stuck()
                  case OutOfFuel() => OutOfFuel()
                }
              } else {
                Ok(false)
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          case _ => Ok(false)
        })
      case ADTV(c, xs) =>
        ((b) match {
          case ADTV(d, ys) => (if ((c == d)) {
              values_eq(v_P, xs, ys)
            } else {
              Ok(false)
            })
          case _ => Ok(false)
        })
      case ArrayV(xs) =>
        ((b) match {
          case ArrayV(ys) => values_eq(v_P, xs, ys)
          case _ => Ok(false)
        })
    }

    def values_eq(v_P: Program, xs: List[Value], ys: List[Value]): Result[Boolean] =
      ((xs) match {
        case Nil() => ((ys) match {
            case Nil() => Ok(true)
            case _ => Ok(false)
          })
        case Cons(x, xr) => ((ys) match {
            case Nil() => Ok(false)
            case Cons(y, yr) => value_eq(v_P, x, y) match {
                case Ok(same) => (if (same) {
                  values_eq(v_P, xr, yr)
                } else {
                  Ok(false)
                })
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
          })
      })

    def eval_and(v_P: Program, fuel: BigInt, env: Env, es: List[Expr]): Result[Value] =
      ((es) match {
        case Nil() => Ok(BoolV(true))
        case Cons(e, rest) => eval_bool(v_P, fuel, env, e) match {
            case Ok(b) => (if (b) {
              eval_and(v_P, fuel, env, rest)
            } else {
              Ok(BoolV(false))
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def eval_or(v_P: Program, fuel: BigInt, env: Env, es: List[Expr]): Result[Value] =
      ((es) match {
        case Nil() => Ok(BoolV(false))
        case Cons(e, rest) => eval_bool(v_P, fuel, env, e) match {
            case Ok(b) => (if (b) {
              Ok(BoolV(true))
            } else {
              eval_or(v_P, fuel, env, rest)
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def apply(v_P: Program, fuel: BigInt, f: Value, vs: List[Value]): Result[Value] =
      ((f) match {
        case ClosureV(params, body, Env(tys, vars)) => (if ((fuel <= BigInt(0))) {
            OutOfFuel()
          } else {
            bind_all(param_ids(params), vs) match {
              case Ok(bs) => eval(v_P, (fuel - BigInt(1)), Env(tys, append_env(bs, vars)), body)
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          })
        case _ => Stuck()
      })

    def append_env(bs: List[Binding], env: List[Binding]): List[Binding] =
      ((bs) match {
        case Nil() => env
        case Cons(b, rest) => Cons(b, append_env(rest, env))
      })

    def nth(vs: List[Value], i: BigInt): Result[Value] =
      ((vs) match {
        case Nil() => Stuck()
        case Cons(v, rest) => (if ((i == BigInt(1))) {
            Ok(v)
          } else {
            nth(rest, (i - BigInt(1)))
          })
      })

    def abs(a: BigInt): BigInt =
      (if ((a < BigInt(0))) {
        (BigInt(0) - a)
      } else {
        a
      })

    def gcd(a: BigInt, b: BigInt): BigInt =
      (if ((b == BigInt(0))) {
        a
      } else {
        gcd(b, emod(a, b))
      })

    def pow2(n: BigInt): BigInt =
      (if ((n <= BigInt(0))) {
        BigInt(1)
      } else {
        (BigInt(2) * pow2((n - BigInt(1))))
      })

    def bit(a: BigInt): BigInt =
      emod(a, BigInt(2))

    def bit_and(a: BigInt, b: BigInt): BigInt =
      (if (((a <= BigInt(0)) || (b <= BigInt(0)))) {
        BigInt(0)
      } else {
        ((BigInt(2) * bit_and(ediv(a, BigInt(2)), ediv(b, BigInt(2)))) + (bit(a) * bit(b)))
      })

    def bit_or(a: BigInt, b: BigInt): BigInt =
      (if ((a <= BigInt(0))) {
        b
      } else {
        (if ((b <= BigInt(0))) {
          a
        } else {
          ((BigInt(2) * bit_or(ediv(a, BigInt(2)), ediv(b, BigInt(2)))) + ((bit(a) + bit(b)) - (bit(a) * bit(b))))
        })
      })

    def bit_xor(a: BigInt, b: BigInt): BigInt =
      (if ((a <= BigInt(0))) {
        b
      } else {
        (if ((b <= BigInt(0))) {
          a
        } else {
          ((BigInt(2) * bit_xor(ediv(a, BigInt(2)), ediv(b, BigInt(2)))) + emod((bit(a) + bit(b)), BigInt(2)))
        })
      })

    def tdiv(a: BigInt, b: BigInt): BigInt =
      (if ((BigInt(0) <= a)) {
        ediv(a, b)
      } else {
        (BigInt(0) - ediv((BigInt(0) - a), b))
      })

    def trem(a: BigInt, b: BigInt): BigInt =
      (a - (b * tdiv(a, b)))

    def real(n: BigInt, d: BigInt): Result[Value] =
      (if ((d == BigInt(0))) {
        Stuck()
      } else {
        {
          val g = gcd(abs(n), abs(d))
          val s = (if ((d < BigInt(0))) {
            (BigInt(0) - BigInt(1))
          } else {
            BigInt(1)
          })
          Ok(RealV((s * ediv(n, g)), (s * ediv(d, g))))
        }
      })

    def bv(s: Boolean, w: BigInt, x: BigInt): Value =
      BVV(s, w, emod(x, pow2(w)))

    def twos(w: BigInt, x: BigInt): BigInt =
      (if ((pow2((w - BigInt(1))) <= x)) {
        (x - pow2(w))
      } else {
        x
      })

    def bv_int(s: Boolean, w: BigInt, x: BigInt): BigInt =
      (if (s) {
        twos(w, x)
      } else {
        x
      })

    def same_bv(s: Boolean, w: BigInt, t: Boolean, v: BigInt): Boolean =
      ((s == t) && (w == v))

    def arith_plus(a: Value, b: Value): Result[Value] =
      ((a) match {
        case IntV(x) => ((b) match {
            case IntV(y) => Ok(IntV((x + y)))
            case _ => Stuck()
          })
        case RealV(n, d) => ((b) match {
            case RealV(m, e) => real(((n * e) + (m * d)), (d * e))
            case _ => Stuck()
          })
        case BVV(s, w, x) => ((b) match {
            case BVV(t, v, y) => (if (same_bv(s, w, t, v)) {
                Ok(bv(s, w, (x + y)))
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def arith_minus(a: Value, b: Value): Result[Value] =
      ((a) match {
        case IntV(x) => ((b) match {
            case IntV(y) => Ok(IntV((x - y)))
            case _ => Stuck()
          })
        case RealV(n, d) => ((b) match {
            case RealV(m, e) => real(((n * e) - (m * d)), (d * e))
            case _ => Stuck()
          })
        case BVV(s, w, x) => ((b) match {
            case BVV(t, v, y) => (if (same_bv(s, w, t, v)) {
                Ok(bv(s, w, (x - y)))
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def arith_times(a: Value, b: Value): Result[Value] =
      ((a) match {
        case IntV(x) => ((b) match {
            case IntV(y) => Ok(IntV((x * y)))
            case _ => Stuck()
          })
        case RealV(n, d) => ((b) match {
            case RealV(m, e) => real((n * m), (d * e))
            case _ => Stuck()
          })
        case BVV(s, w, x) => ((b) match {
            case BVV(t, v, y) => (if (same_bv(s, w, t, v)) {
                Ok(bv(s, w, (x * y)))
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def arith_div(a: Value, b: Value): Result[Value] =
      ((a) match {
        case IntV(x) => ((b) match {
            case IntV(y) => (if ((y == BigInt(0))) {
                Stuck()
              } else {
                Ok(IntV(ediv(x, y)))
              })
            case _ => Stuck()
          })
        case RealV(n, d) => ((b) match {
            case RealV(m, e) => (if ((m == BigInt(0))) {
                Stuck()
              } else {
                real((n * e), (d * m))
              })
            case _ => Stuck()
          })
        case BVV(s, w, x) => ((b) match {
            case BVV(t, v, y) => (if (same_bv(s, w, t, v)) {
                {
                  val i = bv_int(s, w, x)
                  val j = bv_int(s, w, y)
                  (if ((j == BigInt(0))) {
                    (if (s) {
                      Ok(bv(s, w, (if ((BigInt(0) <= i)) {
                        (BigInt(0) - BigInt(1))
                      } else {
                        BigInt(1)
                      })))
                    } else {
                      Ok(bv(s, w, (pow2(w) - BigInt(1))))
                    })
                  } else {
                    Ok(bv(s, w, tdiv(i, j)))
                  })
                }
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def arith_rem(a: Value, b: Value): Result[Value] =
      ((a) match {
        case IntV(x) => ((b) match {
            case IntV(y) => (if ((y == BigInt(0))) {
                Stuck()
              } else {
                Ok(IntV(emod(x, y)))
              })
            case _ => Stuck()
          })
        case BVV(s, w, x) => ((b) match {
            case BVV(t, v, y) => (if (same_bv(s, w, t, v)) {
                {
                  val i = bv_int(s, w, x)
                  val j = bv_int(s, w, y)
                  (if ((j == BigInt(0))) {
                    Ok(a)
                  } else {
                    Ok(bv(s, w, trem(i, j)))
                  })
                }
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def arith_mod(a: Value, b: Value): Result[Value] =
      ((a) match {
        case IntV(x) => ((b) match {
            case IntV(y) => (if ((y == BigInt(0))) {
                Stuck()
              } else {
                Ok(IntV(emod(x, y)))
              })
            case _ => Stuck()
          })
        case BVV(s, w, x) => ((b) match {
            case BVV(t, v, y) => (if (same_bv(s, w, t, v)) {
                {
                  val i = bv_int(s, w, x)
                  val j = bv_int(s, w, y)
                  (if ((j == BigInt(0))) {
                    Ok(a)
                  } else {
                    {
                      val r = emod(i, j)
                      Ok(bv(s, w, (if (((j < BigInt(0)) && !((r == BigInt(0))))) {
                        (r + j)
                      } else {
                        r
                      })))
                    }
                  })
                }
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def arith_neg(a: Value): Result[Value] =
      ((a) match {
        case IntV(x) => Ok(IntV((BigInt(0) - x)))
        case RealV(n, d) => Ok(RealV((BigInt(0) - n), d))
        case BVV(s, w, x) => Ok(bv(s, w, (BigInt(0) - x)))
        case _ => Stuck()
      })

    def arith_lt(a: Value, b: Value): Result[Boolean] =
      ((a) match {
        case IntV(x) => ((b) match {
            case IntV(y) => Ok((x < y))
            case _ => Stuck()
          })
        case RealV(n, d) => ((b) match {
            case RealV(m, e) => Ok(((n * e) < (m * d)))
            case _ => Stuck()
          })
        case CharV(x) => ((b) match {
            case CharV(y) => Ok((x < y))
            case _ => Stuck()
          })
        case BVV(s, w, x) => ((b) match {
            case BVV(t, v, y) => (if (same_bv(s, w, t, v)) {
                Ok((bv_int(s, w, x) < bv_int(s, w, y)))
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def arith_le(a: Value, b: Value): Result[Boolean] =
      arith_lt(b, a) match {
        case Ok(lt) => Ok(!(lt))
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def shift_amount(w: BigInt, y: BigInt): BigInt =
      (if ((w <= y)) {
        w
      } else {
        y
      })

    def bit_op(op: BitOp, s: Boolean, w: BigInt, x: BigInt, y: BigInt): Value =
      {
        val k = pow2(shift_amount(w, y))
        ((op) match {
          case AndOp() => BVV(s, w, bit_and(x, y))
          case OrOp() => BVV(s, w, bit_or(x, y))
          case XorOp() => BVV(s, w, bit_xor(x, y))
          case ShiftLeftOp() => bv(s, w, (x * k))
          case AShiftRightOp() => bv(s, w, ediv(twos(w, x), k))
          case LShiftRightOp() => BVV(s, w, ediv(x, k))
        })
      }

    def bv_binary(op: BitOp, a: Value, b: Value): Result[Value] =
      ((a) match {
        case BVV(s, w, x) => ((b) match {
            case BVV(t, v, y) => (if (same_bv(s, w, t, v)) {
                Ok(bit_op(op, s, w, x, y))
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def bv_cast(a: Value, v: BigInt): Result[Value] =
      ((a) match {
        case BVV(s, w, x) => Ok(bv(s, v, bv_int(s, w, x)))
        case _ => Stuck()
      })

    def rat_add(a: Rat, b: Rat): Rat =
      ((a) match {
        case Rat(n, d) => ((b) match {
            case Rat(m, k) => Rat(((n * k) + (m * d)), (d * k))
          })
      })

    def rat_mul(a: Rat, b: Rat): Rat =
      ((a) match {
        case Rat(n, d) => ((b) match {
            case Rat(m, k) => Rat((n * m), (d * k))
          })
      })

    def rat_div(a: Rat, b: Rat): Rat =
      ((a) match {
        case Rat(n, d) => ((b) match {
            case Rat(m, k) => (if ((m < BigInt(0))) {
                Rat((BigInt(0) - (n * k)), (BigInt(0) - (d * m)))
              } else {
                Rat((n * k), (d * m))
              })
          })
      })

    def rat_num(a: Rat): BigInt =
      ((a) match {
        case Rat(n, _) => n
      })

    def rat_cmp(a: Rat, b: Rat): BigInt =
      ((a) match {
        case Rat(n, d) => ((b) match {
            case Rat(m, k) => (if (((n * k) < (m * d))) {
                (BigInt(0) - BigInt(1))
              } else {
                (if (((n * k) == (m * d))) {
                  BigInt(0)
                } else {
                  BigInt(1)
                })
              })
          })
      })

    def bitlen(n: BigInt): BigInt =
      (if ((n <= BigInt(0))) {
        BigInt(0)
      } else {
        (BigInt(1) + bitlen(ediv(n, BigInt(2))))
      })

    def rat_ilog2(a: Rat): BigInt =
      ((a) match {
        case Rat(n, d) => {
            val k = (bitlen(n) - bitlen(d))
            (if ((k < BigInt(0))) {
              (if (((n * pow2((BigInt(0) - k))) < d)) {
                (k - BigInt(1))
              } else {
                k
              })
            } else {
              (if ((n < (d * pow2(k)))) {
                (k - BigInt(1))
              } else {
                k
              })
            })
          }
      })

    def isqrt_from(n: BigInt, x: BigInt): BigInt =
      {
        val y = ediv((x + ediv(n, x)), BigInt(2))
        (if (((BigInt(0) < y) && (y < x))) {
          isqrt_from(n, y)
        } else {
          x
        })
      }

    def isqrt(n: BigInt): BigInt =
      (if ((n <= BigInt(0))) {
        BigInt(0)
      } else {
        isqrt_from(n, pow2(ediv((bitlen(n) + BigInt(1)), BigInt(2))))
      })

    def fp_bias(e: BigInt): BigInt =
      (pow2((e - BigInt(1))) - BigInt(1))

    def fp_max_exp(e: BigInt): BigInt =
      (pow2(e) - BigInt(1))

    def fp_sign(e: BigInt, s: BigInt, x: BigInt): Boolean =
      (pow2(((e + s) - BigInt(1))) <= x)

    def fp_exp(e: BigInt, s: BigInt, x: BigInt): BigInt =
      emod(ediv(x, pow2((s - BigInt(1)))), pow2(e))

    def fp_frac(s: BigInt, x: BigInt): BigInt =
      emod(x, pow2((s - BigInt(1))))

    def fp_nan(e: BigInt, s: BigInt, x: BigInt): Boolean =
      ((fp_exp(e, s, x) == fp_max_exp(e)) && !((fp_frac(s, x) == BigInt(0))))

    def fp_inf(e: BigInt, s: BigInt, x: BigInt): Boolean =
      ((fp_exp(e, s, x) == fp_max_exp(e)) && (fp_frac(s, x) == BigInt(0)))

    def fp_zero(e: BigInt, s: BigInt, x: BigInt): Boolean =
      ((fp_exp(e, s, x) == BigInt(0)) && (fp_frac(s, x) == BigInt(0)))

    def fp_bits(e: BigInt, s: BigInt, neg: Boolean, be: BigInt, f: BigInt): BigInt =
      ((if (neg) {
        pow2(((e + s) - BigInt(1)))
      } else {
        BigInt(0)
      }) + ((be * pow2((s - BigInt(1)))) + f))

    def fp_nan_bits(e: BigInt, s: BigInt): BigInt =
      fp_bits(e, s, false, fp_max_exp(e), pow2((s - BigInt(2))))

    def fp_inf_bits(e: BigInt, s: BigInt, neg: Boolean): BigInt =
      fp_bits(e, s, neg, fp_max_exp(e), BigInt(0))

    def fp_zero_bits(e: BigInt, s: BigInt, neg: Boolean): BigInt =
      fp_bits(e, s, neg, BigInt(0), BigInt(0))

    def fp_canonical(e: BigInt, s: BigInt, x: BigInt): BigInt =
      (if (fp_nan(e, s, x)) {
        fp_nan_bits(e, s)
      } else {
        x
      })

    def fp_rat(e: BigInt, s: BigInt, x: BigInt): Rat =
      {
        val be = fp_exp(e, s, x)
        val f = fp_frac(s, x)
        {
          val m = (if ((be == BigInt(0))) {
            f
          } else {
            (f + pow2((s - BigInt(1))))
          })
          val k = (((if ((be == BigInt(0))) {
            BigInt(1)
          } else {
            be
          }) - fp_bias(e)) - (s - BigInt(1)))
          val sg = (if (fp_sign(e, s, x)) {
            (BigInt(0) - BigInt(1))
          } else {
            BigInt(1)
          })
          (if ((k < BigInt(0))) {
            Rat((sg * m), pow2((BigInt(0) - k)))
          } else {
            Rat((sg * (m * pow2(k))), BigInt(1))
          })
        }
      }

    def round_up(rm: RoundingMode, neg: Boolean, i: BigInt, c: BigInt, inexact: Boolean): Boolean =
      (if (!(inexact)) {
        false
      } else {
        ((rm) match {
          case RNE() => ((BigInt(0) < c) || ((c == BigInt(0)) && (emod(i, BigInt(2)) == BigInt(1))))
          case RNA() => (BigInt(0) <= c)
          case RTP() => !(neg)
          case RTN() => neg
          case RTZ() => false
        })
      })

    def sign_cmp(a: BigInt, b: BigInt): BigInt =
      (if ((a < b)) {
        (BigInt(0) - BigInt(1))
      } else {
        (if ((a == b)) {
          BigInt(0)
        } else {
          BigInt(1)
        })
      })

    def fp_overflow(rm: RoundingMode, e: BigInt, s: BigInt, neg: Boolean): BigInt =
      (if (((rm) match {
        case RNE() => true
        case RNA() => true
        case RTP() => !(neg)
        case RTN() => neg
        case RTZ() => false
      })) {
        fp_inf_bits(e, s, neg)
      } else {
        fp_bits(e, s, neg, (fp_max_exp(e) - BigInt(1)), (pow2((s - BigInt(1))) - BigInt(1)))
      })

    def fp_pack(rm: RoundingMode, e: BigInt, s: BigInt, neg: Boolean, qe: BigInt, m: BigInt): BigInt =
      {
        val carry = (m == pow2(s))
        {
          val m2 = (if (carry) {
            pow2((s - BigInt(1)))
          } else {
            m
          })
          val qe2 = (if (carry) {
            (qe + BigInt(1))
          } else {
            qe
          })
          (if ((m2 == BigInt(0))) {
            fp_zero_bits(e, s, neg)
          } else {
            (if ((m2 < pow2((s - BigInt(1))))) {
              fp_bits(e, s, neg, BigInt(0), m2)
            } else {
              {
                val be = ((qe2 + (s - BigInt(1))) + fp_bias(e))
                (if ((fp_max_exp(e) <= be)) {
                  fp_overflow(rm, e, s, neg)
                } else {
                  fp_bits(e, s, neg, be, (m2 - pow2((s - BigInt(1)))))
                })
              }
            })
          })
        }
      }

    def scaled(n: BigInt, d: BigInt, p: BigInt): Rat =
      (if ((p < BigInt(0))) {
        Rat(n, (d * pow2((BigInt(0) - p))))
      } else {
        Rat((n * pow2(p)), d)
      })

    def fp_round(rm: RoundingMode, e: BigInt, s: BigInt, q: Rat): BigInt =
      ((q) match {
        case Rat(n, d) => {
            val neg = (n < BigInt(0))
            {
              val a = Rat(abs(n), d)
              val emin = (BigInt(1) - fp_bias(e))
              {
                val k = rat_ilog2(a)
                {
                  val qe = ((if ((k < emin)) {
                    emin
                  } else {
                    k
                  }) - (s - BigInt(1)))
                  ((scaled(abs(n), d, (BigInt(0) - qe))) match {
                    case Rat(sn, sd) => {
                        val i = ediv(sn, sd)
                        val r = emod(sn, sd)
                        fp_pack(rm, e, s, neg, qe, (i + (if (round_up(rm, neg, i, sign_cmp((BigInt(2) * r), sd), !((r == BigInt(0))))) {
                          BigInt(1)
                        } else {
                          BigInt(0)
                        })))
                      }
                  })
                }
              }
            }
          }
      })

    def fp_of_rat(rm: RoundingMode, e: BigInt, s: BigInt, q: Rat): BigInt =
      (if ((rat_num(q) == BigInt(0))) {
        fp_zero_bits(e, s, false)
      } else {
        fp_round(rm, e, s, q)
      })

    def round_rat_int(rm: RoundingMode, q: Rat): BigInt =
      ((q) match {
        case Rat(n, d) => {
            val neg = (n < BigInt(0))
            {
              val i = ediv(abs(n), d)
              val r = emod(abs(n), d)
              {
                val m = (i + (if (round_up(rm, neg, i, sign_cmp((BigInt(2) * r), d), !((r == BigInt(0))))) {
                  BigInt(1)
                } else {
                  BigInt(0)
                }))
                (if (neg) {
                  (BigInt(0) - m)
                } else {
                  m
                })
              }
            }
          }
      })

    def is_rtn(rm: RoundingMode): Boolean =
      ((rm) match {
        case RTN() => true
        case _ => false
      })

    def fp_add(rm: RoundingMode, e: BigInt, s: BigInt, x: BigInt, y: BigInt): BigInt =
      (if ((fp_nan(e, s, x) || fp_nan(e, s, y))) {
        fp_nan_bits(e, s)
      } else {
        (if (fp_inf(e, s, x)) {
          (if ((fp_inf(e, s, y) && !((fp_sign(e, s, x) == fp_sign(e, s, y))))) {
            fp_nan_bits(e, s)
          } else {
            x
          })
        } else {
          (if (fp_inf(e, s, y)) {
            y
          } else {
            {
              val q = rat_add(fp_rat(e, s, x), fp_rat(e, s, y))
              (if ((rat_num(q) == BigInt(0))) {
                (if (((fp_zero(e, s, x) && fp_zero(e, s, y)) && (fp_sign(e, s, x) == fp_sign(e, s, y)))) {
                  x
                } else {
                  fp_zero_bits(e, s, is_rtn(rm))
                })
              } else {
                fp_round(rm, e, s, q)
              })
            }
          })
        })
      })

    def fp_neg(e: BigInt, s: BigInt, x: BigInt): BigInt =
      (if (fp_nan(e, s, x)) {
        fp_nan_bits(e, s)
      } else {
        (if (fp_sign(e, s, x)) {
          (x - pow2(((e + s) - BigInt(1))))
        } else {
          (x + pow2(((e + s) - BigInt(1))))
        })
      })

    def fp_abs(e: BigInt, s: BigInt, x: BigInt): BigInt =
      (if (fp_sign(e, s, x)) {
        fp_neg(e, s, x)
      } else {
        fp_canonical(e, s, x)
      })

    def fp_mul(rm: RoundingMode, e: BigInt, s: BigInt, x: BigInt, y: BigInt): BigInt =
      {
        val neg = !((fp_sign(e, s, x) == fp_sign(e, s, y)))
        (if ((fp_nan(e, s, x) || fp_nan(e, s, y))) {
          fp_nan_bits(e, s)
        } else {
          (if ((fp_inf(e, s, x) || fp_inf(e, s, y))) {
            (if ((fp_zero(e, s, x) || fp_zero(e, s, y))) {
              fp_nan_bits(e, s)
            } else {
              fp_inf_bits(e, s, neg)
            })
          } else {
            (if ((fp_zero(e, s, x) || fp_zero(e, s, y))) {
              fp_zero_bits(e, s, neg)
            } else {
              fp_round(rm, e, s, rat_mul(fp_rat(e, s, x), fp_rat(e, s, y)))
            })
          })
        })
      }

    def fp_div(rm: RoundingMode, e: BigInt, s: BigInt, x: BigInt, y: BigInt): BigInt =
      {
        val neg = !((fp_sign(e, s, x) == fp_sign(e, s, y)))
        (if (((fp_nan(e, s, x) || fp_nan(e, s, y)) || ((fp_inf(e, s, x) && fp_inf(e, s, y)) || (fp_zero(e, s, x) && fp_zero(e, s, y))))) {
          fp_nan_bits(e, s)
        } else {
          (if (fp_inf(e, s, x)) {
            fp_inf_bits(e, s, neg)
          } else {
            (if (fp_inf(e, s, y)) {
              fp_zero_bits(e, s, neg)
            } else {
              (if (fp_zero(e, s, y)) {
                fp_inf_bits(e, s, neg)
              } else {
                (if (fp_zero(e, s, x)) {
                  fp_zero_bits(e, s, neg)
                } else {
                  fp_round(rm, e, s, rat_div(fp_rat(e, s, x), fp_rat(e, s, y)))
                })
              })
            })
          })
        })
      }

    def fp_fma(rm: RoundingMode, e: BigInt, s: BigInt, x: BigInt, y: BigInt, z: BigInt): BigInt =
      {
        val neg = !((fp_sign(e, s, x) == fp_sign(e, s, y)))
        (if (((fp_nan(e, s, x) || fp_nan(e, s, y)) || fp_nan(e, s, z))) {
          fp_nan_bits(e, s)
        } else {
          (if ((fp_inf(e, s, x) || fp_inf(e, s, y))) {
            (if (((fp_zero(e, s, x) || fp_zero(e, s, y)) || (fp_inf(e, s, z) && !((fp_sign(e, s, z) == neg))))) {
              fp_nan_bits(e, s)
            } else {
              fp_inf_bits(e, s, neg)
            })
          } else {
            (if (fp_inf(e, s, z)) {
              z
            } else {
              {
                val q = rat_add(rat_mul(fp_rat(e, s, x), fp_rat(e, s, y)), fp_rat(e, s, z))
                (if ((rat_num(q) == BigInt(0))) {
                  (if (((fp_zero(e, s, x) || fp_zero(e, s, y)) && (fp_zero(e, s, z) && (fp_sign(e, s, z) == neg)))) {
                    z
                  } else {
                    fp_zero_bits(e, s, is_rtn(rm))
                  })
                } else {
                  fp_round(rm, e, s, q)
                })
              }
            })
          })
        })
      }

    def fp_sqrt(rm: RoundingMode, e: BigInt, s: BigInt, x: BigInt): BigInt =
      (if (fp_nan(e, s, x)) {
        fp_nan_bits(e, s)
      } else {
        (if (fp_zero(e, s, x)) {
          x
        } else {
          (if (fp_sign(e, s, x)) {
            fp_nan_bits(e, s)
          } else {
            (if (fp_inf(e, s, x)) {
              x
            } else {
              ((fp_rat(e, s, x)) match {
                case Rat(n, d) => {
                    val k = ediv(rat_ilog2(Rat(n, d)), BigInt(2))
                    val emin = (BigInt(1) - fp_bias(e))
                    {
                      val qe = ((if ((k < emin)) {
                        emin
                      } else {
                        k
                      }) - (s - BigInt(1)))
                      ((scaled(n, d, (BigInt(2) - (BigInt(2) * qe)))) match {
                        case Rat(sn, sd) => {
                            val m = ediv(sn, sd)
                            val exact = (emod(sn, sd) == BigInt(0))
                            {
                              val t = isqrt(m)
                              {
                                val i = ediv(t, BigInt(2))
                                val half = (emod(t, BigInt(2)) == BigInt(1))
                                val sticky = (!(exact) || !(((t * t) == m)))
                                {
                                  val c = (if (half) {
                                    (if (sticky) {
                                      BigInt(1)
                                    } else {
                                      BigInt(0)
                                    })
                                  } else {
                                    (BigInt(0) - BigInt(1))
                                  })
                                  fp_pack(rm, e, s, false, qe, (i + (if (round_up(rm, false, i, c, (half || sticky))) {
                                    BigInt(1)
                                  } else {
                                    BigInt(0)
                                  })))
                                }
                              }
                            }
                          }
                      })
                    }
                  }
              })
            })
          })
        })
      })

    def fp_round_integral(rm: RoundingMode, e: BigInt, s: BigInt, x: BigInt): BigInt =
      (if (((fp_nan(e, s, x) || fp_inf(e, s, x)) || fp_zero(e, s, x))) {
        fp_canonical(e, s, x)
      } else {
        {
          val m = round_rat_int(rm, fp_rat(e, s, x))
          (if ((m == BigInt(0))) {
            fp_zero_bits(e, s, fp_sign(e, s, x))
          } else {
            fp_round(rm, e, s, Rat(m, BigInt(1)))
          })
        }
      })

    def fp_cmp(e: BigInt, s: BigInt, x: BigInt, y: BigInt): BigInt =
      (if (fp_inf(e, s, x)) {
        (if ((fp_inf(e, s, y) && (fp_sign(e, s, x) == fp_sign(e, s, y)))) {
          BigInt(0)
        } else {
          (if (fp_sign(e, s, x)) {
            (BigInt(0) - BigInt(1))
          } else {
            BigInt(1)
          })
        })
      } else {
        (if (fp_inf(e, s, y)) {
          (if (fp_sign(e, s, y)) {
            BigInt(1)
          } else {
            (BigInt(0) - BigInt(1))
          })
        } else {
          rat_cmp(fp_rat(e, s, x), fp_rat(e, s, y))
        })
      })

    def fp_max(e: BigInt, s: BigInt, x: BigInt, y: BigInt, max: Boolean): BigInt =
      (if (fp_nan(e, s, x)) {
        fp_canonical(e, s, y)
      } else {
        (if (fp_nan(e, s, y)) {
          x
        } else {
          (if ((fp_zero(e, s, x) && fp_zero(e, s, y))) {
            (if ((max == fp_sign(e, s, x))) {
              y
            } else {
              x
            })
          } else {
            (if ((max == (fp_cmp(e, s, x, y) < BigInt(0)))) {
              y
            } else {
              x
            })
          })
        })
      })

    def fp_to_int(rm: RoundingMode, e: BigInt, s: BigInt, x: BigInt, lo: BigInt, hi: BigInt): BigInt =
      (if (fp_nan(e, s, x)) {
        BigInt(0)
      } else {
        (if (fp_inf(e, s, x)) {
          (if (fp_sign(e, s, x)) {
            lo
          } else {
            hi
          })
        } else {
          {
            val m = round_rat_int(rm, fp_rat(e, s, x))
            (if ((m < lo)) {
              lo
            } else {
              (if ((hi < m)) {
                hi
              } else {
                m
              })
            })
          }
        })
      })

    def fp_cast(rm: RoundingMode, e: BigInt, s: BigInt, v: Value): Result[BigInt] =
      ((v) match {
        case FPV(e2, s2, x) => (if (fp_nan(e2, s2, x)) {
            Ok(fp_nan_bits(e, s))
          } else {
            (if (fp_inf(e2, s2, x)) {
              Ok(fp_inf_bits(e, s, fp_sign(e2, s2, x)))
            } else {
              (if (fp_zero(e2, s2, x)) {
                Ok(fp_zero_bits(e, s, fp_sign(e2, s2, x)))
              } else {
                Ok(fp_round(rm, e, s, fp_rat(e2, s2, x)))
              })
            })
          })
        case BVV(sg, w, x) => Ok(fp_of_rat(rm, e, s, Rat(bv_int(sg, w, x), BigInt(1))))
        case RealV(n, d) => Ok(fp_of_rat(rm, e, s, Rat(n, d)))
        case _ => Stuck()
      })

    def eval_rm(v_P: Program, fuel: BigInt, env: Env, e: Expr): Result[RoundingMode] =
      eval(v_P, fuel, env, e) match {
        case Ok(v) => ((v) match {
          case RoundingModeV(rm) => Ok(rm)
          case _ => Stuck()
        })
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def fp_op(op: FPOp, rm: RoundingMode, e: BigInt, s: BigInt, x: BigInt, y: BigInt): BigInt =
      ((op) match {
        case FPAddOp() => fp_add(rm, e, s, x, y)
        case FPSubOp() => fp_add(rm, e, s, x, fp_neg(e, s, y))
        case FPMulOp() => fp_mul(rm, e, s, x, y)
        case FPDivOp() => fp_div(rm, e, s, x, y)
        case FPMinOp() => fp_max(e, s, x, y, false)
        case FPMaxOp() => fp_max(e, s, x, y, true)
      })

    def fp_binary(op: FPOp, rm: RoundingMode, a: Value, b: Value): Result[Value] =
      ((a) match {
        case FPV(e, s, x) => ((b) match {
            case FPV(e2, s2, y) => (if (((e == e2) && (s == s2))) {
                Ok(FPV(e, s, fp_op(op, rm, e, s, x, y)))
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def fp_rel(rel: FPRel, a: Value, b: Value): Result[Value] =
      ((a) match {
        case FPV(e, s, x) => ((b) match {
            case FPV(e2, s2, y) => (if (((e == e2) && (s == s2))) {
                (if ((fp_nan(e, s, x) || fp_nan(e, s, y))) {
                  Ok(BoolV(false))
                } else {
                  {
                    val c = fp_cmp(e, s, x, y)
                    ((rel) match {
                      case FPEqRel() => Ok(BoolV((c == BigInt(0))))
                      case FPLtRel() => Ok(BoolV((c < BigInt(0))))
                      case FPLeRel() => Ok(BoolV((c <= BigInt(0))))
                    })
                  }
                })
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def fp_class(k: FPClass, v: Value): Result[Value] =
      ((v) match {
        case FPV(e, s, x) => {
            val be = fp_exp(e, s, x)
            val nan = fp_nan(e, s, x)
            ((k) match {
              case ZeroClass() => Ok(BoolV(fp_zero(e, s, x)))
              case InfiniteClass() => Ok(BoolV(fp_inf(e, s, x)))
              case NaNClass() => Ok(BoolV(nan))
              case NegativeClass() => Ok(BoolV((!(nan) && fp_sign(e, s, x))))
              case PositiveClass() => Ok(BoolV((!(nan) && !(fp_sign(e, s, x)))))
              case NormalClass() => Ok(BoolV((!((be == BigInt(0))) && !((be == fp_max_exp(e))))))
              case SubnormalClass() => Ok(BoolV(((be == BigInt(0)) && !(fp_zero(e, s, x)))))
            })
          }
        case _ => Stuck()
      })

    def append_chars(xs: List[BigInt], ys: List[BigInt]): List[BigInt] =
      ((xs) match {
        case Nil() => ys
        case Cons(x, rest) => Cons(x, append_chars(rest, ys))
      })

    def length(xs: List[BigInt]): BigInt =
      ((xs) match {
        case Nil() => BigInt(0)
        case Cons(_, rest) => (BigInt(1) + length(rest))
      })

    def take(n: BigInt, xs: List[BigInt]): List[BigInt] =
      (if ((n <= BigInt(0))) {
        Nil()
      } else {
        ((xs) match {
          case Nil() => Nil()
          case Cons(x, rest) => Cons(x, take((n - BigInt(1)), rest))
        })
      })

    def drop(n: BigInt, xs: List[BigInt]): List[BigInt] =
      (if ((n <= BigInt(0))) {
        xs
      } else {
        ((xs) match {
          case Nil() => Nil()
          case Cons(_, rest) => drop((n - BigInt(1)), rest)
        })
      })

    def eval_string(v_P: Program, fuel: BigInt, env: Env, e: Expr): Result[List[BigInt]] =
      eval(v_P, fuel, env, e) match {
        case Ok(v) => ((v) match {
          case StringV(cs) => Ok(cs)
          case _ => Stuck()
        })
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def set_contains(v_P: Program, xs: List[Value], v: Value): Result[Boolean] =
      ((xs) match {
        case Nil() => Ok(false)
        case Cons(x, rest) => value_eq(v_P, x, v) match {
            case Ok(same) => (if (same) {
              Ok(true)
            } else {
              set_contains(v_P, rest, v)
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def set_insert(v_P: Program, xs: List[Value], v: Value): Result[List[Value]] =
      set_contains(v_P, xs, v) match {
        case Ok(in) => (if (in) {
          Ok(xs)
        } else {
          Ok(Cons(v, xs))
        })
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def set_insert_all(v_P: Program, xs: List[Value], vs: List[Value]): Result[List[Value]] =
      ((vs) match {
        case Nil() => Ok(xs)
        case Cons(v, rest) => set_insert(v_P, xs, v) match {
            case Ok(ys) => set_insert_all(v_P, ys, rest)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def subset(v_P: Program, xs: List[Value], ys: List[Value]): Result[Boolean] =
      ((xs) match {
        case Nil() => Ok(true)
        case Cons(x, rest) => set_contains(v_P, ys, x) match {
            case Ok(in) => (if (in) {
              subset(v_P, rest, ys)
            } else {
              Ok(false)
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def set_filter(v_P: Program, xs: List[Value], ys: List[Value], keep: Boolean): Result[List[Value]] =
      ((xs) match {
        case Nil() => Ok(Nil())
        case Cons(x, rest) => set_contains(v_P, ys, x) match {
            case Ok(in) => set_filter(v_P, rest, ys, keep) match {
              case Ok(zs) => (if ((in == keep)) {
                Ok(Cons(x, zs))
              } else {
                Ok(zs)
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def eval_set(v_P: Program, fuel: BigInt, env: Env, e: Expr): Result[List[Value]] =
      eval(v_P, fuel, env, e) match {
        case Ok(v) => ((v) match {
          case SetV(xs) => Ok(xs)
          case _ => Stuck()
        })
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def bag_get(v_P: Program, xs: List[BagEntry], v: Value): Result[BigInt] =
      ((xs) match {
        case Nil() => Ok(BigInt(0))
        case Cons(BagEntry(x, n), rest) => value_eq(v_P, x, v) match {
            case Ok(same) => (if (same) {
              Ok(n)
            } else {
              bag_get(v_P, rest, v)
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def bag_remove(v_P: Program, xs: List[BagEntry], v: Value): Result[List[BagEntry]] =
      ((xs) match {
        case Nil() => Ok(Nil())
        case Cons(BagEntry(x, n), rest) => value_eq(v_P, x, v) match {
            case Ok(same) => (if (same) {
              Ok(rest)
            } else {
              bag_remove(v_P, rest, v) match {
                case Ok(ys) => Ok(Cons(BagEntry(x, n), ys))
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def bag_set(v_P: Program, xs: List[BagEntry], v: Value, n: BigInt): Result[List[BagEntry]] =
      bag_remove(v_P, xs, v) match {
        case Ok(ys) => (if ((BigInt(0) < n)) {
          Ok(Cons(BagEntry(v, n), ys))
        } else {
          Ok(ys)
        })
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def min(a: BigInt, b: BigInt): BigInt =
      (if ((a < b)) {
        a
      } else {
        b
      })

    def bag_combine(op: BagOp, a: BigInt, b: BigInt): BigInt =
      ((op) match {
        case IntersectionOp() => min(a, b)
        case UnionOp() => (a + b)
        case DifferenceOp() => (a - b)
      })

    def bag_merge(v_P: Program, op: BagOp, acc: List[BagEntry], xs: List[BagEntry], ys: List[BagEntry]): Result[List[BagEntry]] =
      ((xs) match {
        case Nil() => Ok(acc)
        case Cons(BagEntry(x, n), rest) => bag_get(v_P, ys, x) match {
            case Ok(m) => bag_set(v_P, acc, x, bag_combine(op, n, m)) match {
              case Ok(acc2) => bag_merge(v_P, op, acc2, rest, ys)
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def bag_add_all(v_P: Program, acc: List[BagEntry], xs: List[BagEntry]): Result[List[BagEntry]] =
      ((xs) match {
        case Nil() => Ok(acc)
        case Cons(BagEntry(x, n), rest) => bag_get(v_P, acc, x) match {
            case Ok(m) => bag_set(v_P, acc, x, (m + n)) match {
              case Ok(acc2) => bag_add_all(v_P, acc2, rest)
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def sub_bag(v_P: Program, xs: List[BagEntry], ys: List[BagEntry]): Result[Boolean] =
      ((xs) match {
        case Nil() => Ok(true)
        case Cons(BagEntry(x, n), rest) => bag_get(v_P, ys, x) match {
            case Ok(m) => (if ((n == m)) {
              sub_bag(v_P, rest, ys)
            } else {
              Ok(false)
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def eval_bag(v_P: Program, fuel: BigInt, env: Env, e: Expr): Result[List[BagEntry]] =
      eval(v_P, fuel, env, e) match {
        case Ok(v) => ((v) match {
          case BagV(xs) => Ok(xs)
          case _ => Stuck()
        })
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def eval_bag_entries(v_P: Program, fuel: BigInt, env: Env, acc: List[BagEntry], es: List[ExprPair]): Result[List[BagEntry]] =
      ((es) match {
        case Nil() => Ok(acc)
        case Cons(ExprPair(k, c), rest) => eval(v_P, fuel, env, k) match {
            case Ok(v) => eval_int(v_P, fuel, env, c) match {
              case Ok(n) => bag_set(v_P, acc, v, n) match {
                case Ok(acc2) => eval_bag_entries(v_P, fuel, env, acc2, rest)
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def map_get(v_P: Program, xs: List[MapEntry], k: Value, d: Value): Result[Value] =
      ((xs) match {
        case Nil() => Ok(d)
        case Cons(MapEntry(x, v), rest) => value_eq(v_P, x, k) match {
            case Ok(same) => (if (same) {
              Ok(v)
            } else {
              map_get(v_P, rest, k, d)
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def map_remove(v_P: Program, xs: List[MapEntry], k: Value): Result[List[MapEntry]] =
      ((xs) match {
        case Nil() => Ok(Nil())
        case Cons(MapEntry(x, v), rest) => value_eq(v_P, x, k) match {
            case Ok(same) => (if (same) {
              Ok(rest)
            } else {
              map_remove(v_P, rest, k) match {
                case Ok(ys) => Ok(Cons(MapEntry(x, v), ys))
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def map_put(v_P: Program, xs: List[MapEntry], k: Value, v: Value): Result[List[MapEntry]] =
      map_remove(v_P, xs, k) match {
        case Ok(ys) => Ok(Cons(MapEntry(k, v), ys))
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def same_entries(v_P: Program, ks: List[MapEntry], xs: List[MapEntry], d: Value, ys: List[MapEntry], e: Value): Result[Boolean] =
      ((ks) match {
        case Nil() => Ok(true)
        case Cons(MapEntry(k, _), rest) => map_get(v_P, xs, k, d) match {
            case Ok(a) => map_get(v_P, ys, k, e) match {
              case Ok(b) => value_eq(v_P, a, b) match {
                case Ok(same) => (if (same) {
                  same_entries(v_P, rest, xs, d, ys, e)
                } else {
                  Ok(false)
                })
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def map_without(v_P: Program, xs: List[MapEntry], ks: List[Value]): Result[List[MapEntry]] =
      ((xs) match {
        case Nil() => Ok(Nil())
        case Cons(MapEntry(k, v), rest) => set_contains(v_P, ks, k) match {
            case Ok(in) => map_without(v_P, rest, ks) match {
              case Ok(ys) => (if (in) {
                Ok(ys)
              } else {
                Ok(Cons(MapEntry(k, v), ys))
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def map_take(v_P: Program, acc: List[MapEntry], ks: List[Value], xs: List[MapEntry], d: Value): Result[List[MapEntry]] =
      ((ks) match {
        case Nil() => Ok(acc)
        case Cons(k, rest) => map_get(v_P, xs, k, d) match {
            case Ok(v) => map_put(v_P, acc, k, v) match {
              case Ok(acc2) => map_take(v_P, acc2, rest, xs, d)
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def eval_map_entries(v_P: Program, fuel: BigInt, env: Env, acc: List[MapEntry], es: List[ExprPair]): Result[List[MapEntry]] =
      ((es) match {
        case Nil() => Ok(acc)
        case Cons(ExprPair(k, v), rest) => eval(v_P, fuel, env, k) match {
            case Ok(kv) => eval(v_P, fuel, env, v) match {
              case Ok(vv) => map_put(v_P, acc, kv, vv) match {
                case Ok(acc2) => eval_map_entries(v_P, fuel, env, acc2, rest)
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def resolve(tenv: List[TypeBinding], t: Type): Type =
      ((t) match {
        case TypeParameter(x) => ((lookup_type(tenv, x)) match {
            case Some(TypeBinding(_, u, uenv)) => resolve(uenv, u)
            case None() => t
          })
        case TupleType(ts) => TupleType(resolve_all(tenv, ts))
        case SetType(u) => SetType(resolve(tenv, u))
        case BagType(u) => BagType(resolve(tenv, u))
        case MapType(u, w) => MapType(resolve(tenv, u), resolve(tenv, w))
        case FunctionType(ts, u) => FunctionType(resolve_all(tenv, ts), resolve(tenv, u))
        case ADTType(s, ts) => ADTType(s, resolve_all(tenv, ts))
        case RefinementType(x, u, prop) => RefinementType(x, resolve(tenv, u), prop)
        case PiType(ps, u) => PiType(resolve_params(tenv, ps), resolve(tenv, u))
        case SigmaType(ps, u) => SigmaType(resolve_params(tenv, ps), resolve(tenv, u))
        case _ => t
      })

    def resolve_params(tenv: List[TypeBinding], ps: List[Param]): List[Param] =
      ((ps) match {
        case Nil() => Nil()
        case Cons(Param(x, t), rest) => Cons(Param(x, resolve(tenv, t)), resolve_params(tenv, rest))
      })

    def resolve_all(tenv: List[TypeBinding], ts: List[Type]): List[Type] =
      ((ts) match {
        case Nil() => Nil()
        case Cons(t, rest) => Cons(resolve(tenv, t), resolve_all(tenv, rest))
      })

    def lookup_interpretation(is: List[Interpretation], f: Id, tps: List[Type]): Result[Interpretation] =
      ((is) match {
        case Nil() => Stuck()
        case Cons(i, rest) => ((i) match {
            case Interpretation(g, us, _, _) => (if (((f == g) && (tps == us))) {
                Ok(i)
              } else {
                lookup_interpretation(rest, f, tps)
              })
          })
      })

    def has_type(v_P: Program, env: Env, v: Value, t: Type): Boolean = t match {
      case IntegerType() =>
        ((v) match {
          case IntV(_) => true
          case _ => false
        })
      case BooleanType() =>
        ((v) match {
          case BoolV(_) => true
          case _ => false
        })
      case UnitType() =>
        ((v) match {
          case UnitV() => true
          case _ => false
        })
      case CharType() =>
        ((v) match {
          case CharV(c) => ((BigInt(0) <= c) && (c < BigInt(65536)))
          case _ => false
        })
      case RealType() =>
        ((v) match {
          case RealV(n, d) => ((BigInt(0) < d) && (gcd(abs(n), d) == BigInt(1)))
          case _ => false
        })
      case StringType() =>
        ((v) match {
          case StringV(cs) => valid_chars(cs)
          case _ => false
        })
      case BVType(s, w) =>
        ((v) match {
          case BVV(s2, w2, x) => (((s == s2) && (w == w2)) && ((BigInt(0) <= x) && (x < pow2(w))))
          case _ => false
        })
      case FPType(e, s) =>
        ((v) match {
          case FPV(e2, s2, x) => (((e == e2) && (s == s2)) && (((BigInt(0) <= x) && (x < pow2((e + s)))) && (x == fp_canonical(e, s, x))))
          case _ => false
        })
      case RoundingModeType() =>
        ((v) match {
          case RoundingModeV(_) => true
          case _ => false
        })
      case TypeParameter(x) =>
        ((lookup_type(env_types(env), x)) match {
          case Some(TypeBinding(_, u, uenv)) => has_type(v_P, Env(uenv, Nil()), v, u)
          case None() => ((v) match {
              case IntV(_) => true
              case _ => false
            })
        })
      case TupleType(ts) =>
        ((v) match {
          case TupleV(vs) => have_types(v_P, env, vs, ts)
          case _ => false
        })
      case SetType(u) =>
        ((v) match {
          case SetV(xs) => (all_have_type(v_P, env, xs, u) && distinct_values(v_P, xs))
          case _ => false
        })
      case BagType(u) =>
        ((v) match {
          case BagV(xs) => (bag_has_type(v_P, env, xs, u) && distinct_values(v_P, bag_elems(xs)))
          case _ => false
        })
      case MapType(u, w) =>
        ((v) match {
          case MapV(xs, d) => (has_type(v_P, env, d, w) && (map_has_type(v_P, env, xs, u, w) && distinct_values(v_P, map_keys(xs))))
          case _ => false
        })
      case FunctionType(from, to) =>
        ((v) match {
          case ClosureV(params, _, _) => (same_arity(params, from) && function_has_type(v_P, env, v, from, to))
          case _ => false
        })
      case ADTType(s, args) =>
        ((v) match {
          case ADTV(c, vs) => ((v_P) match {
              case Program(_, cs, ss, _, _) => ((lookup_ctor(cs, c)) match {
                  case Ok(Constructor(_, s2, fields)) => ((lookup_sort(ss, s)) match {
                      case Ok(Sort(_, tparams, inv)) => ((s == s2) && (params_have_types(v_P, Env(bind_types(tparams, args, env_types(env)), Nil()), vs, fields) && ((inv) match {
                          case None() => true
                          case Some(f) => invariant_holds(v_P, f, args, env_types(env), v)
                        })))
                      case _ => false
                    })
                  case _ => false
                })
            })
          case _ => false
        })
      case RefinementType(x, u, prop) =>
        (has_type(v_P, env, v, u) && holds(v_P, env_bind(env, x, v), prop))
      case PropType() =>
        ((v) match {
          case BoolV(_) => true
          case _ => false
        })
      case PiType(ps, to) =>
        ((v) match {
          case ClosureV(params, _, _) => (same_arity(params, param_types(ps)) && pi_has_type(v_P, env, v, ps, to))
          case _ => false
        })
      case SigmaType(ps, to) =>
        ((v) match {
          case TupleV(vs) => sigma_has_type(v_P, env, vs, ps, to)
          case _ => false
        })
      case ArrayType(base) =>
        ((v) match {
          case ArrayV(vs) => (all_have_type(v_P, env, vs, base) && (values_length(vs) < pow2(BigInt(31))))
          case _ => false
        })
    }

    /** `holds` in the semantics, which quantifies over values: an oracle gives it. */
    def holds(v_P: Program, env: Env, prop: Expr): Boolean

    /** `invariant-holds` in the semantics, which quantifies over values: an oracle gives it. */
    def invariant_holds(v_P: Program, f: Id, args: List[Type], tenv: List[TypeBinding], v: Value): Boolean

    /** `function-has-type` in the semantics, which quantifies over values: an oracle gives it. */
    def function_has_type(v_P: Program, env: Env, f: Value, from: List[Type], to: Type): Boolean

    /** `pi-has-type` in the semantics, which quantifies over values: an oracle gives it. */
    def pi_has_type(v_P: Program, env: Env, f: Value, ps: List[Param], to: Type): Boolean

    def sigma_has_type(v_P: Program, env: Env, vs: List[Value], ps: List[Param], to: Type): Boolean =
      ((ps) match {
        case Nil() => ((vs) match {
            case Cons(v, Nil()) => has_type(v_P, env, v, to)
            case _ => false
          })
        case Cons(Param(x, t), more) => ((vs) match {
            case Cons(v, rest) => (has_type(v_P, env, v, t) && sigma_has_type(v_P, env_bind(env, x, v), rest, more, to))
            case _ => false
          })
      })

    def param_types(ps: List[Param]): List[Type] =
      ((ps) match {
        case Nil() => Nil()
        case Cons(Param(_, t), rest) => Cons(t, param_types(rest))
      })

    def have_types(v_P: Program, env: Env, vs: List[Value], ts: List[Type]): Boolean =
      ((vs) match {
        case Nil() => ((ts) match {
            case Nil() => true
            case _ => false
          })
        case Cons(v, rest) => ((ts) match {
            case Nil() => false
            case Cons(t, more) => (has_type(v_P, env, v, t) && have_types(v_P, env, rest, more))
          })
      })

    def params_have_types(v_P: Program, env: Env, vs: List[Value], ps: List[Param]): Boolean =
      ((vs) match {
        case Nil() => ((ps) match {
            case Nil() => true
            case _ => false
          })
        case Cons(v, rest) => ((ps) match {
            case Nil() => false
            case Cons(Param(x, t), more) => (has_type(v_P, env, v, t) && params_have_types(v_P, env_bind(env, x, v), rest, more))
          })
      })

    def all_have_type(v_P: Program, env: Env, vs: List[Value], t: Type): Boolean =
      ((vs) match {
        case Nil() => true
        case Cons(v, rest) => (has_type(v_P, env, v, t) && all_have_type(v_P, env, rest, t))
      })

    def bag_has_type(v_P: Program, env: Env, xs: List[BagEntry], t: Type): Boolean =
      ((xs) match {
        case Nil() => true
        case Cons(BagEntry(x, n), rest) => (((BigInt(0) < n) && has_type(v_P, env, x, t)) && bag_has_type(v_P, env, rest, t))
      })

    def map_has_type(v_P: Program, env: Env, xs: List[MapEntry], t: Type, u: Type): Boolean =
      ((xs) match {
        case Nil() => true
        case Cons(MapEntry(k, v), rest) => ((has_type(v_P, env, k, t) && has_type(v_P, env, v, u)) && map_has_type(v_P, env, rest, t, u))
      })

    def valid_chars(cs: List[BigInt]): Boolean =
      ((cs) match {
        case Nil() => true
        case Cons(c, rest) => (((BigInt(0) <= c) && (c <= BigInt(196607))) && valid_chars(rest))
      })

    def distinct_values(v_P: Program, xs: List[Value]): Boolean =
      ((xs) match {
        case Nil() => true
        case Cons(x, rest) => ((set_contains(v_P, rest, x) == Ok(false)) && distinct_values(v_P, rest))
      })

    def bag_elems(xs: List[BagEntry]): List[Value] =
      ((xs) match {
        case Nil() => Nil()
        case Cons(BagEntry(x, _), rest) => Cons(x, bag_elems(rest))
      })

    def map_keys(xs: List[MapEntry]): List[Value] =
      ((xs) match {
        case Nil() => Nil()
        case Cons(MapEntry(k, _), rest) => Cons(k, map_keys(rest))
      })

    def same_arity(ps: List[Param], ts: List[Type]): Boolean =
      ((ps) match {
        case Nil() => ((ts) match {
            case Nil() => true
            case _ => false
          })
        case Cons(_, rest) => ((ts) match {
            case Nil() => false
            case Cons(_, more) => same_arity(rest, more)
          })
      })

    def instance(v_P: Program, fuel: BigInt, env: Env, params: List[Param], vs: List[Value], body: Expr): Result[Value] =
      ((env) match {
        case Env(tys, vars) => bind_all(param_ids(params), vs) match {
            case Ok(bs) => eval(v_P, fuel, Env(tys, append_env(bs, vars)), body)
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    /** `forall-result` in the semantics, which quantifies over values: an oracle gives it. */
    def forall_result(v_P: Program, fuel: BigInt, env: Env, params: List[Param], body: Expr): Result[Value]

    /** `closures-equal` in the semantics, which quantifies over values: an oracle gives it. */
    def closures_equal(v_P: Program, f: Value, g: Value): Boolean

    def lookup_vars(vars: List[Binding], ids: List[Id]): Result[List[Binding]] =
      ((ids) match {
        case Nil() => Ok(Nil())
        case Cons(x, rest) => lookup_var(vars, x) match {
            case Ok(v) => lookup_vars(vars, rest) match {
              case Ok(bs) => Ok(Cons(Binding(x, v), bs))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def eval_cases(v_P: Program, fuel: BigInt, env: Env, v: Value, cases: List[MatchCase], none: Result[Value]): Result[Value] =
      ((cases) match {
        case Nil() => none
        case Cons(MatchCase(pat, guard, rhs), rest) => match_pattern(v_P, fuel, env, v, pat) match {
            case Ok(m) => ((m) match {
              case None() => eval_cases(v_P, fuel, env, v, rest, none)
              case Some(bs) => ((env) match {
                  case Env(tys, vars) => {
                      val inner = Env(tys, append_env(bs, vars))
                      ((guard) match {
                        case None() => eval(v_P, fuel, inner, rhs)
                        case Some(g) => eval_bool(v_P, fuel, inner, g) match {
                            case Ok(b) => (if (b) {
                              eval(v_P, fuel, inner, rhs)
                            } else {
                              eval_cases(v_P, fuel, env, v, rest, none)
                            })
                            case Stuck() => Stuck()
                            case OutOfFuel() => OutOfFuel()
                          }
                      })
                    }
                })
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def bind_binder(b: Option[Id], v: Value, bs: List[Binding]): List[Binding] =
      ((b) match {
        case None() => bs
        case Some(x) => Cons(Binding(x, v), bs)
      })

    def add_binder(b: Option[Id], v: Value, m: Option[List[Binding]]): Option[List[Binding]] =
      ((m) match {
        case None() => None()
        case Some(bs) => Some(bind_binder(b, v, bs))
      })

    def match_pattern(v_P: Program, fuel: BigInt, env: Env, v: Value, p: Pattern): Result[Option[List[Binding]]] =
      ((p) match {
        case WildcardPattern(b) => Ok(Some(bind_binder(b, v, Nil())))
        case ADTPattern(b, c, subs) => ((v) match {
            case ADTV(d, vs) => (if ((c == d)) {
                match_patterns(v_P, fuel, env, vs, subs) match {
                  case Ok(m) => Ok(add_binder(b, v, m))
                  case Stuck() => Stuck()
                  case OutOfFuel() => OutOfFuel()
                }
              } else {
                Ok(None())
              })
            case _ => Stuck()
          })
        case TuplePattern(b, subs) => ((v) match {
            case TupleV(vs) => match_patterns(v_P, fuel, env, vs, subs) match {
                case Ok(m) => Ok(add_binder(b, v, m))
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
            case _ => Stuck()
          })
        case LiteralPattern(b, lit) => eval(v_P, fuel, env, lit) match {
            case Ok(l) => value_eq(v_P, v, l) match {
              case Ok(same) => (if (same) {
                Ok(Some(bind_binder(b, v, Nil())))
              } else {
                Ok(None())
              })
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
        case AlternativePattern(b, subs) => match_any(v_P, fuel, env, v, subs) match {
            case Ok(any) => (if (any) {
              Ok(Some(bind_binder(b, v, Nil())))
            } else {
              Ok(None())
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
        case RefinementPattern(under, x, pred) => match_pattern(v_P, fuel, env, v, under) match {
            case Ok(m) => ((m) match {
              case None() => Ok(None())
              case Some(bs) => eval_bool(v_P, fuel, env_bind(env, x, v), pred) match {
                  case Ok(b) => (if (b) {
                    Ok(Some(bs))
                  } else {
                    Ok(None())
                  })
                  case Stuck() => Stuck()
                  case OutOfFuel() => OutOfFuel()
                }
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
        case UnapplyPattern(b, recs, f, tps, is_empty, is_empty_tps, get, get_tps, subs) => eval_list(v_P, fuel, env, recs) match {
            case Ok(rs) => call(v_P, fuel, f, tps, env_types(env), append_values(rs, Cons(v, Nil()))) match {
              case Ok(u) => call(v_P, fuel, is_empty, is_empty_tps, env_types(env), Cons(u, Nil())) match {
                case Ok(e) => ((e) match {
                  case BoolV(true) => Ok(None())
                  case BoolV(false) => call(v_P, fuel, get, get_tps, env_types(env), Cons(u, Nil())) match {
                      case Ok(g) => match_patterns(v_P, fuel, env, unapplied(g, patterns_length(subs)), subs) match {
                        case Ok(m) => Ok(add_binder(b, v, m))
                        case Stuck() => Stuck()
                        case OutOfFuel() => OutOfFuel()
                      }
                      case Stuck() => Stuck()
                      case OutOfFuel() => OutOfFuel()
                    }
                  case _ => Stuck()
                })
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def unapplied(g: Value, n: BigInt): List[Value] =
      (if ((n == BigInt(1))) {
        Cons(g, Nil())
      } else {
        ((g) match {
          case TupleV(vs) => vs
          case _ => Nil()
        })
      })

    def patterns_length(ps: List[Pattern]): BigInt =
      ((ps) match {
        case Nil() => BigInt(0)
        case Cons(_, rest) => (BigInt(1) + patterns_length(rest))
      })

    def match_any(v_P: Program, fuel: BigInt, env: Env, v: Value, ps: List[Pattern]): Result[Boolean] =
      ((ps) match {
        case Nil() => Ok(false)
        case Cons(p, rest) => match_pattern(v_P, fuel, env, v, p) match {
            case Ok(m) => ((m) match {
              case None() => match_any(v_P, fuel, env, v, rest)
              case Some(_) => Ok(true)
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def match_patterns(v_P: Program, fuel: BigInt, env: Env, vs: List[Value], ps: List[Pattern]): Result[Option[List[Binding]]] =
      ((ps) match {
        case Nil() => ((vs) match {
            case Nil() => Ok(Some(Nil()))
            case _ => Stuck()
          })
        case Cons(p, rest) => ((vs) match {
            case Nil() => Stuck()
            case Cons(v, others) => match_pattern(v_P, fuel, env, v, p) match {
                case Ok(m) => ((m) match {
                  case None() => Ok(None())
                  case Some(bs) => match_patterns(v_P, fuel, env, others, rest) match {
                      case Ok(n) => ((n) match {
                        case None() => Ok(None())
                        case Some(cs) => Ok(Some(append_env(bs, cs)))
                      })
                      case Stuck() => Stuck()
                      case OutOfFuel() => OutOfFuel()
                    }
                })
                case Stuck() => Stuck()
                case OutOfFuel() => OutOfFuel()
              }
          })
      })

    def append_values(xs: List[Value], ys: List[Value]): List[Value] =
      ((xs) match {
        case Nil() => ys
        case Cons(x, rest) => Cons(x, append_values(rest, ys))
      })

    def zero_divisor(b: Value): Boolean =
      ((b) match {
        case IntV(y) => (y == BigInt(0))
        case BVV(_, _, y) => (y == BigInt(0))
        case _ => false
      })

    def jvm_shift(op: BitOp, a: Value, b: Value): Result[Value] =
      ((a) match {
        case BVV(s, w, x) => ((b) match {
            case BVV(t, v, y) => (if (same_bv(s, w, t, v)) {
                Ok(bit_op(op, s, w, x, emod(y, w)))
              } else {
                Stuck()
              })
            case _ => Stuck()
          })
        case _ => Stuck()
      })

    def eval_array(v_P: Program, fuel: BigInt, env: Env, e: Expr): Result[List[Value]] =
      eval(v_P, fuel, env, e) match {
        case Ok(a) => ((a) match {
          case ArrayV(vs) => Ok(vs)
          case _ => Stuck()
        })
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def eval_index(v_P: Program, fuel: BigInt, env: Env, e: Expr): Result[BigInt] =
      eval(v_P, fuel, env, e) match {
        case Ok(a) => ((a) match {
          case BVV(s, w, x) => Ok(bv_int(s, w, x))
          case _ => Stuck()
        })
        case Stuck() => Stuck()
        case OutOfFuel() => OutOfFuel()
      }

    def eval_entries(v_P: Program, fuel: BigInt, env: Env, es: List[ArrayEntry]): Result[List[ArrayEntryValue]] =
      ((es) match {
        case Nil() => Ok(Nil())
        case Cons(ArrayEntry(i, e), rest) => eval(v_P, fuel, env, e) match {
            case Ok(v) => eval_entries(v_P, fuel, env, rest) match {
              case Ok(vs) => Ok(Cons(ArrayEntryValue(i, v), vs))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
      })

    def entry_at(es: List[ArrayEntryValue], i: BigInt, d: Value): Value =
      ((es) match {
        case Nil() => d
        case Cons(ArrayEntryValue(j, v), rest) => (if ((i == j)) {
            v
          } else {
            entry_at(rest, i, d)
          })
      })

    def array_fill(i: BigInt, n: BigInt, d: Value, es: List[ArrayEntryValue]): List[Value] =
      (if ((n <= i)) {
        Nil()
      } else {
        Cons(entry_at(es, i, d), array_fill((i + BigInt(1)), n, d, es))
      })

    def array_get(vs: List[Value], i: BigInt): Result[Value] =
      ((vs) match {
        case Nil() => Stuck()
        case Cons(v, rest) => (if ((i == BigInt(0))) {
            Ok(v)
          } else {
            array_get(rest, (i - BigInt(1)))
          })
      })

    def array_set(vs: List[Value], i: BigInt, v: Value): Result[List[Value]] =
      ((vs) match {
        case Nil() => Stuck()
        case Cons(w, rest) => (if ((i == BigInt(0))) {
            Ok(Cons(v, rest))
          } else {
            array_set(rest, (i - BigInt(1)), v) match {
              case Ok(ws) => Ok(Cons(w, ws))
              case Stuck() => Stuck()
              case OutOfFuel() => OutOfFuel()
            }
          })
      })

    def values_length(vs: List[Value]): BigInt =
      ((vs) match {
        case Nil() => BigInt(0)
        case Cons(_, rest) => (BigInt(1) + values_length(rest))
      })

    def int_max(vs: List[Value]): Result[Value] =
      ((vs) match {
        case Cons(IntV(x), Nil()) => Ok(IntV(x))
        case Cons(IntV(x), rest) => int_max(rest) match {
            case Ok(m) => ((m) match {
              case IntV(y) => Ok(IntV((if ((x < y)) {
                  y
                } else {
                  x
                })))
              case _ => Stuck()
            })
            case Stuck() => Stuck()
            case OutOfFuel() => OutOfFuel()
          }
        case _ => Stuck()
      })
  }
}
