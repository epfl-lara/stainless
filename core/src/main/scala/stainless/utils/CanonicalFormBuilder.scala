/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package utils

import extraction.xlang.{ trees => xt }

import scala.collection.mutable.{ ArrayBuffer, Map => MutableMap }

/**
 * Build canonical forms for functions and classes, making it easy to compare the
 * equivalence of two functions, **or** two classes (but not one function and one class).
 */
object CanonicalFormBuilder {
  def apply(fd: xt.FunDef): CanonicalForm = {
    val impl = new CanonicalFormBuilderImpl
    impl.build(fd)
  }

  def apply(cd: xt.ClassDef): CanonicalForm = {
    val impl = new CanonicalFormBuilderImpl
    impl.build(cd)
  }
}

/** Canonical form for functions, expressions, ... */
class CanonicalForm(val bytes: Array[Byte]) {
  override lazy val hashCode: Int = java.util.Arrays.hashCode(bytes)

  override def equals(other: Any): Boolean = other match {
    // Because cf.bytes == bytes doesn't work, obviously.
    case cf: CanonicalForm =>
      (bytes.length == cf.bytes.length) &&
      ((bytes zip cf.bytes) forall { p => p._1 == p._2 })

    case _ => false
  }
}

/**
 * Core implementation of the canonisation algorithm.
 *
 * NOTE A single usage of [[build]] per instance is allowed!
 *
 * Internal representation of various data/expressions:
 *  - Free variables are represented using unique 16-bit integers, see [[UID]].
 *  - A unique & constant code is used to represent an expression.
 *  - A unique & constant code is used to represent a type.
 *  - Variable length sequences are prefixed by their size.
 *
 * The produced sequence of bytes is unambiguous because types and expressions are all
 * prefixed by a unique code. This also means the original data could be reconstructed,
 * in theory -- but the format wasn't designed to do that so it's expected to be ugly.
 *
 * NOTE When adding new trees, one needs to carefully update both [[storeTypeSpecifics]]
 *      and [[storeExprSpecifics]] so that the types/expressions are mapped to a unique
 *      sequence of bytes. The contract is that, for two types (or expressions), the
 *      bytes should be equal iff the two are equivalent. The [[typeMapping]] and
 *      [[exprMapping]] at the bottom should also be updated.
 */
private class CanonicalFormBuilderImpl {
  import CanonicalFormBuilderImpl.{ exprMapping, typeMapping }

  /******************* Public Interface ***********************************************************/

  def build(fd: xt.FunDef): CanonicalForm = {
    // Format is:
    //  - number of type parameters
    //  - number of parameters
    //  - for each parameter, its type
    //  - the return type
    //  - add flags
    //  - the body
    registerId(fd.id)
    storeLength(fd.tparams.size)
    fd.tparams foreach registerTP
    storeLength(fd.params.size)
    fd.params foreach { vd =>
      registerVD(vd)
      storeType(vd.tpe)
      storeFlags(vd.flags)
    }
    storeType(fd.returnType)
    storeFlags(fd.flags)
    storeExpr(fd.fullBody)

    new CanonicalForm(buffer.toArray)
  }


  def build(cd: xt.ClassDef): CanonicalForm = {
    // Format is:
    //  - number of type parameters
    //  - number of parents
    //  - each parent type
    //  - number of fields
    //  - each field
    //  - add flags
    storeLength(cd.tparams.size)
    cd.tparams foreach registerTP
    storeLength(cd.parents.size)
    cd.parents foreach storeType
    storeLength(cd.fields.size)
    cd.fields foreach { vd =>
      storeId(vd.id)
      storeType(vd.tpe)
      storeFlags(vd.flags)
    }
    storeFlags(cd.flags)

    new CanonicalForm(buffer.toArray)
  }


  /******************* Internal State *************************************************************/

  private type UID = Short

  /** Hold mapping between **local** variables and [[UID]]. */
  private val mapping = MutableMap[Identifier, UID]()

  /** This one gets filled as we traverse the AST. */
  private val buffer = ArrayBuffer[Byte]()


  /******************* Internal Helpers ***********************************************************/

  /** Register a new, unique & fresh UID for the given [[id]]. */
  private val registerId: Identifier => Unit = {
    var nextId: UID = 0
    def regFn: Identifier => Unit = { id =>
      assert(nextId != -1) // waaay too many UID were used! (after wrap around)
      val uid = nextId
      mapping += id -> uid
      nextId = (nextId + 1).toShort // safely wraps around, thankfully!
    }
    regFn
  }

  /** Idem, but for Type Parameter. */
  private def registerTP(tpd: xt.TypeParameterDef): Unit = {
    registerId(tpd.id)
  }

  /** Idem, but for ValDef. */
  private def registerVD(vd: xt.ValDef): Unit = {
    registerId(vd.id)
  }

  private def storeId(id: Identifier): Unit = {
    // The format is:
    //  - flag indicating whether it's a local variable or not
    //  - if local, the UID, otherwise the string representing the variable's id
    mapping get id match {
      case None =>
        storeBool(false)
        storeString(id.uniqueName)

      case Some(uid) =>
        storeBool(true)
        storeUID(uid)
    }
  }

  /** Store information relative to [[e]]. */
  private def storeExpr(e: xt.Expr): Unit = {
    val code = exprMapping get e.getClass getOrElse {
      /* Expression was not listed in [[exprMapping]] */
      throw new java.lang.IllegalArgumentException(s"Unknown code for expression ${e.getClass}")
    }

    // Use the deconstructor to extract **most** of the expression's information.
    val (ids, vars, es, tps, _) = xt.deconstructor.deconstruct(e)

    // Format is:
    //  - expression code
    //  - expression specifics
    //  - number of variables
    //  - each variable
    //  - number of types
    //  - each type
    //  - number of subexpressions
    //  - each subexpression
    storeByte(code)
    storeExprSpecifics(e)
    storeLength(vars.size)
    vars foreach storeVariable
    storeLength(tps.size)
    tps foreach storeType
    storeLength(es.size)
    es foreach storeExpr
  }

  private def storeExprSpecifics(e: xt.Expr): Unit = e match {
    // NOTE this part partly depends on the extractor implementation.

    case xt.Let(vd, _, _) => registerVD(vd)
    case xt.Lambda(vds, _) => vds foreach registerVD
    case xt.Forall(vds, _) => vds foreach registerVD
    case xt.Choose(vd, _) => registerVD(vd)
    case xt.FunctionInvocation(id, _, _) => storeId(id)
    case xt.CharLiteral(l) => storeChar(l)
    case l @ xt.BVLiteral(_, size) => storeInt(size); storeBigInt(l.toBigInt)
    case xt.IntegerLiteral(l) => storeBigInt(l)
    case xt.FractionLiteral(n, d) => storeBigInt(n); storeBigInt(d)
    case xt.BooleanLiteral(l) => storeBool(l)
    case xt.StringLiteral(l) => storeString(l)
    case xt.GenericValue(tp, id) => storeType(tp); storeInt(id)
    case xt.ADTSelector(_, sel) => storeId(sel)
    case xt.TupleSelect(_, index) => storeInt(index)

    case xt.Error(_, desc) => storeString(desc)

    case xt.Assert(_, descOpt, _) => descOpt match {
      case None => storeBool(false)
      case Some(desc) => storeBool(true); storeString(desc)
    }

    case xt.Annotated(_, flags) => storeFlags(flags.toSet)

    case xt.MatchExpr(_, cases) =>
      def rec(p: xt.Pattern): Unit = {
        val (_, vs, _, _, subs, _) = xt.deconstructor.deconstruct(p)
        vs map { _.toVal } foreach registerVD
        subs foreach rec
      }

      storeLength(cases.size)
      cases foreach { case xt.MatchCase(p, _, _) => rec(p) }

    case xt.LargeArray(elems, _, _, _) =>
      val idx = elems.keySet.toSeq.sorted
      storeLength(idx.size)
      idx foreach storeInt

    case xt.LetVar(vd, _, _) => registerVD(vd)
    case xt.FieldAssignment(_, sel, _) => storeId(sel)

    case xt.LetRec(fds, _) =>
      storeLength(fds.size)
      fds foreach { case xt.LocalFunDef(vd, tps, _) =>
        registerVD(vd)
        storeLength(tps.size)
        tps foreach registerTP
      }

    case xt.MethodInvocation(_, id, _, _) => storeId(id)
    case xt.ClassSelector(_, sel) => storeId(sel)

    case _ => // Nothing
  }


  /** Store information relative to [[typ]], similar to [[storeExpr]]. */
  private def storeType(typ: xt.Type): Unit = {
    val code = typeMapping get typ.getClass getOrElse {
      /* Type was not listed in [[typeMapping]] */
      throw new java.lang.IllegalArgumentException(s"Unknown code for type ${typ.getClass}")
    }

    val (_, tps, _, _) = xt.deconstructor.deconstruct(typ)

    // Format is:
    //  - type code
    //  - type specifics
    //  - number of subtypes
    //  - each subtype
    storeByte(code)
    storeTypeSpecifics(typ)
    storeLength(tps.size)
    tps foreach storeType
  }

  private def storeTypeSpecifics(typ: xt.Type): Unit = typ match {
    case xt.BVType(size) => storeInt(size)
    case xt.TypeParameter(id, flags) => storeId(id); storeFlags(flags)
    case xt.ADTType(id, _) => storeId(id)

    case _ => // Nothing
  }

  /** Store information relative to [[v]], similar to [[storeExpr]]. */
  private def storeVariable(v: xt.Variable): Unit = {
    // Format is:
    //  - the variable's identifier
    //  - its type
    //  - add flags
    storeId(v.id)
    storeType(v.tpe)
    storeFlags(v.flags)
  }

  /** Store information relative to each of the given [[flags]]. */
  private def storeFlags(flags: Set[xt.Flag]): Unit = {
    storeLength(flags.size)
    // (Arbitrarily) sort the flags for a true canonical form.
    val sorted = flags.toSeq sortBy { _.name }
    sorted foreach { f =>
      storeString(f.name) // the name identify the flag
      f match {
        case xt.Variance(v) => storeBool(v)
        case xt.HasADTInvariant(id) => storeId(id)
        case xt.HasADTEquality(id) => storeId(id)
        case xt.Annotation(_, args) => storeLength(args.size); args foreach { a => storeString(a.toString) }
        case xt.IsMethodOf(id) => storeId(id)
        case xt.Bounds(lo, hi) => storeType(lo); storeType(hi)
        case xt.IsField(isLazy) => storeBool(isLazy)
        case xt.Derived(id) => storeId(id)

        // Nothing specific to add for these:
        case xt.Inline | xt.Implicit | xt.IsVar | xt.IsMutable |
             xt.IsInvariant | xt.IsAbstract | xt.IsSealed | xt.Ignore |
             xt.Extern | xt.Unchecked =>
      }
    }
  }

  private def storeLength(len: Int): Unit = storeInt(len)

  private def storeString(str: String): Unit = {
    storeLength(str.length)
    storeData(str.getBytes)
  }

  private def storeData(bs: Array[Byte]): Unit = buffer ++= bs

  private def storeBool(b: Boolean): Unit = storeByte(if (b) 0 else 1)

  private def storeBigInt(bi: BigInt): Unit = storeString(bi.toString)

  private def storeInt(x: Int): Unit = {
    storeByte((x >>> 24).toByte)
    storeByte((x >>> 16).toByte)
    storeByte((x >>>  8).toByte)
    storeByte((x       ).toByte)
  }

  private def storeChar(c: Char): Unit = {
    storeByte((c >>> 8).toByte)
    storeByte((c      ).toByte)
  }

  private def storeUID(uid: UID): Unit = {
    storeByte((uid >>> 8).toByte)
    storeByte((uid      ).toByte)
  }

  private def storeByte(x: Byte): Unit = buffer += x

}

/** Constants for the implementation. */
private object CanonicalFormBuilderImpl {

  // NOTE We could build those table dynamically, because we don't care about the exact
  //      code for a class as long as it is unique, but this would mean the mappings
  //      would be different across runs and therefore the data could not be saved to disk.
  //      Although we currently don't need that, it remains interesting to be able to do
  //      it in the future, hence those hard-coded mappings.

  /** Mapping from [[xt.Expr]] to a unique, and constant code. */
  private val exprMapping: Map[Class[_], Byte] = {
    Seq[Class[_]](
      classOf[xt.Not],
      classOf[xt.BVNot],
      classOf[xt.UMinus],
      classOf[xt.StringLength],
      classOf[xt.ADTSelector],
      classOf[xt.IsInstanceOf],
      classOf[xt.AsInstanceOf],
      classOf[xt.TupleSelect],
      classOf[xt.Lambda],
      classOf[xt.Forall],
      classOf[xt.Choose],
      classOf[xt.Equals],
      classOf[xt.Implies],
      classOf[xt.Plus],
      classOf[xt.Minus],
      classOf[xt.Times],
      classOf[xt.Division],
      classOf[xt.Remainder],
      classOf[xt.Modulo],
      classOf[xt.LessThan],
      classOf[xt.GreaterThan],
      classOf[xt.LessEquals],
      classOf[xt.GreaterEquals],
      classOf[xt.BVOr],
      classOf[xt.BVAnd],
      classOf[xt.BVXor],
      classOf[xt.BVShiftLeft],
      classOf[xt.BVAShiftRight],
      classOf[xt.BVLShiftRight],
      classOf[xt.BVNarrowingCast],
      classOf[xt.BVWideningCast],
      classOf[xt.StringConcat],
      classOf[xt.SetAdd],
      classOf[xt.ElementOfSet],
      classOf[xt.SubsetOf],
      classOf[xt.SetIntersection],
      classOf[xt.SetUnion],
      classOf[xt.SetDifference],
      classOf[xt.BagAdd],
      classOf[xt.MultiplicityInBag],
      classOf[xt.BagIntersection],
      classOf[xt.BagUnion],
      classOf[xt.BagDifference],
      classOf[xt.MapUpdated],
      classOf[xt.MapApply],
      classOf[xt.Let],
      classOf[xt.Assume],
      classOf[xt.FunctionInvocation],
      classOf[xt.Application],
      classOf[xt.ADT],
      classOf[xt.And],
      classOf[xt.Or],
      classOf[xt.SubString],
      classOf[xt.FiniteSet],
      classOf[xt.FiniteBag],
      classOf[xt.FiniteMap],
      classOf[xt.Tuple],
      classOf[xt.IfExpr],
      classOf[xt.Variable],
      classOf[xt.GenericValue],
      classOf[xt.CharLiteral],
      classOf[xt.BVLiteral],
      classOf[xt.IntegerLiteral],
      classOf[xt.FractionLiteral],
      classOf[xt.BooleanLiteral],
      classOf[xt.StringLiteral],
      classOf[xt.UnitLiteral],

      classOf[xt.Hole],

      classOf[xt.Block],
      classOf[xt.LetVar],
      classOf[xt.Assignment],
      classOf[xt.FieldAssignment],
      classOf[xt.While],
      classOf[xt.ArrayUpdate],
      classOf[xt.Old],
      classOf[xt.BoolBitwiseAnd],
      classOf[xt.BoolBitwiseOr],
      classOf[xt.BoolBitwiseXor],

      classOf[xt.LetRec],
      classOf[xt.ApplyLetRec],

      classOf[xt.MethodInvocation],
      classOf[xt.ClassConstructor],
      classOf[xt.ClassSelector],
      classOf[xt.This],
      classOf[xt.Super],

      classOf[xt.NoTree],
      classOf[xt.Error],
      classOf[xt.Require],
      classOf[xt.Annotated],
      classOf[xt.Ensuring],
      classOf[xt.Assert],
      classOf[xt.MatchExpr],
      classOf[xt.FiniteArray],
      classOf[xt.LargeArray],
      classOf[xt.ArraySelect],
      classOf[xt.ArrayUpdated],
      classOf[xt.ArrayLength],

      classOf[xt.Decreases]
    ).zipWithIndex map { case (c, i) =>
      assert(i <= Byte.MaxValue)
      c -> i.toByte
    }
  }.toMap

  /** Mapping from [[xt.Type]] to a unique, and constant code. */
  private val typeMapping: Map[Class[_], Byte] = {
    Seq[Class[_]](
      classOf[xt.ADTType],
      classOf[xt.TupleType],
      classOf[xt.SetType],
      classOf[xt.BagType],
      classOf[xt.MapType],
      classOf[xt.FunctionType],
      classOf[xt.TypeParameter],
      classOf[xt.BVType],
      classOf[xt.BooleanType],
      classOf[xt.UnitType],
      classOf[xt.CharType],
      classOf[xt.IntegerType],
      classOf[xt.RealType],
      classOf[xt.StringType],

      classOf[xt.ArrayType],
      classOf[xt.ClassType],
      classOf[xt.AnyType],
      classOf[xt.NothingType],
      // classOf[xt.UnionType], // private in oo
      // classOf[xt.IntersectionType], // private in oo
      classOf[xt.TypeBounds],
      xt.Untyped.getClass
    ).zipWithIndex map { case (c, i) =>
      assert(i <= Byte.MaxValue)
      c -> i.toByte
    }
  }.toMap
}

