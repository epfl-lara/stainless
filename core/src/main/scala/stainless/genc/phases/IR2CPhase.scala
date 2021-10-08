/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import ir.IRs.{ SIR }

import ir.PrimitiveTypes._
import ir.Literals._
import ir.Operators._

import genc.{ CAST => C }
import SIR._

import collection.mutable.{ Map => MutableMap, Set => MutableSet }

class IR2CPhase(using override val context: inox.Context) extends LeonPipeline[SIR.Prog, CAST.Prog](context) {
  val name = "CASTer"
  val description = "Translate the IR tree into the final C AST"

  def run(ir: SIR.Prog): CAST.Prog = new IR2CImpl()(using context)(ir)
}

// This implementation is basically a Transformer that produce something which isn't an IR tree.
// So roughly the same visiting scheme is applied.
//
// Function conversion is pretty straighforward at this point of the pipeline. Expression conversion
// require little care. But class conversion is harder; see detailed procedure below.
private class IR2CImpl()(using ctx: inox.Context) {
  def apply(ir: Prog): C.Prog = rec(ir)

  // We use a cache to keep track of the C function, struct, ...
  private val funCache = MutableMap[FunDef, C.Fun]()
  private val structCache = MutableMap[ClassDef, C.Struct]()
  private val unionCache = MutableMap[ClassDef, C.Union]() // For top hierarchy classes only!
  private val enumCache = MutableMap[ClassDef, C.Enum]() // For top hierarchy classes only!
  private val arrayCache = MutableMap[ArrayType, C.Struct]()
  private val headerIncludes = MutableSet[C.Include]()
  private val cIncludes = MutableSet[C.Include]()
  private val typdefs = MutableSet[C.TypeDef]()

  private var dataTypes = Seq[C.DataType]() // For struct & union, keeps track of definition order!

  private def register(dt: C.DataType): Unit = {
    require(!(dataTypes contains dt))

    dataTypes = dataTypes :+ dt
  }

  private def registerHeaderInclude(i: C.Include): Unit = {
    headerIncludes += i
  }

  private def registerCInclude(i: C.Include): Unit = {
    cIncludes += i
  }

  private def register(td: C.TypeDef): Unit = {
    typdefs += td
  }

  private def rec(id: Id) = C.Id(id)

  private def rec(prog: Prog): C.Prog = {

    val decls = prog.decls.map { case (decl, modes) => rec(decl, allowFixedArray = true) match {
      case res: C.Decl => (res, modes)
      case res =>
        ctx.reporter.fatalError(
          "Only simple values are supported as default values for global variables.\n" +
          s"Declaration $decl was translated to $res.\n" +
          (if (decl.vd.typ.isArray && !decl.vd.typ.isFixedArray)
            "Try making the length of the array constant by adding a condition in the class invariant of the global state."
          else
            "")
        )
    }}

    prog.functions foreach rec
    prog.classes foreach rec

    val enums = enumCache.values.toSet
    val functions = funCache.values.toSet

    // Remove "mutability" on includes & typeDefs
    C.Prog(headerIncludes.toSet, cIncludes.toSet, decls, typdefs.toSet, enums, dataTypes, functions)
  }

  private def rec(fd: FunDef): Unit = funCache.getOrElseUpdate(fd, {
    val id = rec(fd.id)
    val returnType = rec(fd.returnType)
    val params = (fd.ctx ++ fd.params).map(rec(_))
    val body = rec(fd.body)

    C.Fun(id, returnType, params, body, fd.isExported, fd.isPure)
  })

  private def rec(fb: FunBody): Either[C.Block, String] = fb match {
    case FunBodyAST(body) =>
      Left(C.buildBlock(rec(body)))

    case FunBodyManual(headerIncludes, cIncludes, body) =>
      headerIncludes foreach { i => registerHeaderInclude(C.Include(i)) }
      cIncludes foreach { i => registerCInclude(C.Include(i)) }
      Right(body)

    case FunDropped(_) => Right("")
  }

  private def rec(cd: ClassDef): Unit = {
    convertClass(cd)
    ()
  }

  private def rec(vd: ValDef): C.Var = {
    // TODO Add const whenever possible, based on e.g. vd.isVar
    val typ = rec(vd.getType)
    val id = rec(vd.id)
    C.Var(id, typ)
  }

  private def rec(typ: Type): C.Type = typ match {
    case PrimitiveType(pt) => C.Primitive(pt)
    case FunType(ctx, params, ret) => C.FunType(params = (ctx ++ params).map(rec(_)), ret = rec(ret))
    case ClassType(clazz) => convertClass(clazz) // can be a struct or an enum
    case array @ ArrayType(_, None) => array2Struct(array)
    case array @ ArrayType(base, Some(length)) => C.FixedArrayType(rec(base), length)
    case ReferenceType(t) => C.Pointer(rec(t))

    case TypeDefType(original, alias, include, exprt) =>
      include foreach { i => registerHeaderInclude(C.Include(i)) }
      val td = C.TypeDef(rec(original), rec(alias), exprt)
      register(td)
      td

    case DroppedType => ??? // void*?
    case NoType => ???
  }

  // One major difference of this rec compared to Transformer.rec(Expr) is that here
  // we don't necessarily follow every branch of the AST. For example, we don't recurse
  // on function definitions, hence no problem with recursive functions.
  private def rec(e: Expr, allowFixedArray: Boolean = false): C.Expr = e match {
    case Binding(vd) => C.Binding(rec(vd.id))

    case Assert(e) => C.Assert(rec(e))

    case MemSet(pointer, value, size) => C.MemSet(rec(pointer), rec(value), rec(size))
    case SizeOf(tpe) => C.SizeOf(rec(tpe))

    case FunRef(e) => rec(e)
    case FunVal(fd) =>
      // We don't recurse on fd here to avoid infinite recursion on recursive functions.
      // Function definition are traversed once from the set of dependencies, or when created
      // artificially (e.g. CmpFactory).
      C.Binding(rec(fd.id))

    case Block(exprs) => C.buildBlock {
      // remove left-over Unit bindings and Unit declarations
      exprs
        .filter {
          case Binding(vd) if vd.typ.isUnitType => false
          case Decl(vd, _) if vd.typ.isUnitType => false
          case e => true
        }
        .map(rec(_))
    }

    case Decl(vd, None) => C.Decl(rec(vd.id), rec(vd.getType), None)

    case Decl(vd, Some(ArrayInit(ArrayAllocStatic(arrayType, length, values0)))) if allowFixedArray && vd.typ.isFixedArray =>
      val values = values0 match {
        case Right(values0) => values0.map(rec(_))
        case Left(_) =>
          // By default, 0-initialisation using only zero value
          val z = arrayType.base match {
            case PrimitiveType(Int8Type) => Int8Lit(0)
            case PrimitiveType(Int32Type) => Int32Lit(0)
            case _ => ctx.reporter.fatalError(s"Unexpected integral type $arrayType")
          }
          Seq(C.Lit(z))
      }
      C.Decl(rec(vd.id), rec(vd.typ), Some(C.ArrayStatic(rec(arrayType.base), values)))

    case Decl(vd, Some(ArrayInit(ArrayAllocStatic(arrayType, length, values0)))) =>
      val bufferId = C.FreshId("buffer")
      val values = values0 match {
        case Right(values0) => values0.map(rec(_))
        case Left(_) =>
          // By default, 0-initialisation using only zero value
          val z = arrayType.base match {
            case PrimitiveType(Int8Type) => Int8Lit(0)
            case PrimitiveType(Int32Type) => Int32Lit(0)
            case _ => ctx.reporter.fatalError(s"Unexpected integral type $arrayType")
          }
          Seq(C.Lit(z))
      }
      val bufferDecl = C.DeclArrayStatic(bufferId, rec(arrayType.base), length, values)
      val data = C.Binding(bufferId)
      val len = C.Lit(Int32Lit(length))
      val array = array2Struct(arrayType)
      val varInit = C.StructInit(array, data :: len :: Nil)
      val varDecl = C.Decl(rec(vd.id), array, Some(varInit))

      C.buildBlock(bufferDecl :: varDecl :: Nil)

    case ArrayInit(ArrayAllocStatic(arrayType, length, values0)) =>
      val values = values0 match {
        case Right(values0) => values0.map(rec(_))
        case Left(_) =>
          // By default, 0-initialisation using only zero value
          val z = arrayType.base match {
            case PrimitiveType(Int8Type) => Int8Lit(0)
            case PrimitiveType(Int32Type) => Int32Lit(0)
            case _ => ctx.reporter.fatalError(s"Unexpected integral type $arrayType")
          }
          Seq(C.Lit(z))
      }
      C.ArrayStatic(rec(arrayType.base), values)

    case Decl(vd, Some(ArrayInit(ArrayAllocVLA(arrayType, length, valueInit)))) =>
      val bufferId = C.FreshId("buffer")
      val lenId = C.FreshId("length")
      val lenDecl = C.Decl(lenId, C.Primitive(Int32Type), Some(rec(length))) // Eval `length` once only
      val len = C.Binding(lenId)
      val bufferDecl = C.DeclArrayVLA(bufferId, rec(arrayType.base), len, rec(valueInit))
      val data = C.Binding(bufferId)
      val array = array2Struct(arrayType)
      val varInit = C.StructInit(array, data :: len :: Nil)
      val varDecl = C.Decl(rec(vd.id), array, Some(varInit))

      C.buildBlock(lenDecl :: bufferDecl :: varDecl :: Nil)

    case Decl(vd, Some(value)) => C.Decl(rec(vd.id), rec(vd.getType), Some(rec(value)))

    case App(FunVal(fd), Seq(), Seq()) if fd.body == FunDropped(true) => C.Binding(rec(fd.id))

    case App(callable, extra, args) => C.Call(rec(callable), (extra ++ args).map(rec(_)))

    case Construct(cd, args) => constructObject(cd, args) // can be a StructInit or an EnumLiteral

    case ArrayInit(alloc) => ctx.reporter.fatalError("This should be part of a Decl expression!")

    // no `data` field for fixed arrays accesses
    case ArrayAccess(FieldAccess(obj, fieldId), index)
      if  obj.getType.isInstanceOf[ClassType] &&
          obj.getType.asInstanceOf[ClassType].clazz.fields.exists(vd =>
            vd.id == fieldId && vd.typ.isFixedArray
          ) =>

      C.ArrayAccess(C.FieldAccess(rec(obj), rec(fieldId)), rec(index))

    // but field accesses of fixed arrays not followed by an array access
    // must be wrapped in an array wrapper struct (see FixedArray.scala example)
    case FieldAccess(obj, fieldId)
      if  obj.getType.isInstanceOf[ClassType] &&
          obj.getType.asInstanceOf[ClassType].clazz.fields.exists(vd =>
            vd.id == fieldId && vd.typ.isFixedArray
          ) =>

      val vd = obj.getType.asInstanceOf[ClassType].clazz.fields.find(vd =>
        vd.id == fieldId && vd.typ.isFixedArray
      ).get
      val arrayType = vd.typ.asInstanceOf[ArrayType]
      val length = arrayType.length.get
      val array = array2Struct(arrayType.copy(length = None))
      C.StructInit(array, C.FieldAccess(rec(obj), rec(fieldId)) :: C.Lit(Int32Lit(length)) :: Nil)

    case FieldAccess(obj, fieldId) => C.FieldAccess(rec(obj), rec(fieldId))

    // no `data` field for fixed arrays accesses
    case ArrayAccess(array, index) if array.getType.isFixedArray => C.ArrayAccess(rec(array), rec(index))
    case ArrayAccess(array, index) => C.ArrayAccess(C.FieldAccess(rec(array), C.Id("data")), rec(index))
    case ArrayLength(array) => C.FieldAccess(rec(array), C.Id("length"))

    case Assign(lhs, rhs) => C.Assign(rec(lhs), rec(rhs))

    /* NOTE For shifting signed integers, we first cast to unsigned, perform the shift operation and
     *      finally cast it back to signed integer. The rational is that overflow is undefined
     *      behaviour in C99 on signed integers and shifts of negative integers is also undefined
     *      behaviour. However, everything is well defined over unsigned integers. The catch is
     *      that casting back from unsigned to signed integer is implementation defined for
     *      values that are negative if we read them using a 2's complement notation. Having a
     *      C compiler that does a normal wrap around is one of the requirement of GenC.
     */
    case BinOp(op, lhs0, rhs0) if op == BLeftShift || op == BRightShift =>
      val tpe = lhs0.getType
      tpe match {
        case PrimitiveType(tpe: IntegralPrimitiveType) if tpe.isSigned =>
          val lhs = C.Cast(rec(lhs0), C.Primitive(tpe.toUnsigned))
          val expr = C.BinOp(op, lhs, rec(rhs0)) // rhs doesn't need to be cast
          C.Cast(expr, C.Primitive(tpe))

        case PrimitiveType(tpe: IntegralPrimitiveType) if tpe.isUnsigned =>
          C.BinOp(op, rec(lhs0), rec(rhs0))

        case _ =>
          ctx.reporter.fatalError(s"Shifting on type $tpe is not supported")
      }

    /* NOTE For == and != on objects, we create a dedicated equal function.
     *      See comment in CmpFactory.
     */
    case BinOp(op @ (Equals | NotEquals), lhs, rhs) if !lhs.getType.isLogical && !lhs.getType.isIntegral && !lhs.getType.isInstanceOf[TypeDefType] =>
      val cmp = CmpFactory(lhs.getType)
      val equals = App(cmp, Seq(), Seq(lhs, rhs))
      val test = if (op == Equals) equals else UnOp(Not, equals)
      rec(test)

    case BinOp(op, lhs, rhs) => C.BinOp(op, rec(lhs), rec(rhs))
    case UnOp(op, expr) => C.UnOp(op, rec(expr))

    case If(cond, thenn) => C.If(rec(cond), C.buildBlock(rec(thenn)))
    case IfElse(cond, thenn, Lit(UnitLit)) => C.If(rec(cond), C.buildBlock(rec(thenn)))
    case IfElse(cond, thenn, elze) => C.IfElse(rec(cond), C.buildBlock(rec(thenn)), C.buildBlock(rec(elze)))
    case While(cond, body) => C.While(rec(cond), C.buildBlock(rec(body)))

    // Find out if we can actually handle IsInstanceOf.
    case IsA(_, ClassType(cd)) if cd.parent.isEmpty => C.True // Since it has typechecked, it can only be true.

    // Currently, classes are tagged with a unique ID per class hierarchy, but
    // without any kind of ordering. This means we cannot have test for membership
    // but only test on concrete children is supported. We could improve on that
    // using something similar to Cohen's encoding.
    case IsA(_, ClassType(cd)) if cd.isAbstract =>
      ctx.reporter.fatalError("Cannot handle membership test with abstract types for now")

    case IsA(expr0, ct) =>
      val tag = getEnumLiteralFor(ct.clazz)
      val expr =
        if (isEnumeration(ct.clazz)) rec(expr0) // It's an enum, therefore no field to access
        else C.FieldAccess(rec(expr0), TaggedUnion.tag)

      C.BinOp(Equals, expr, tag)

    case AsA(expr, ClassType(cd)) if cd.parent.isEmpty => rec(expr) // no casting, actually

    case AsA(expr, ClassType(cd)) if cd.isAbstract =>
      ctx.reporter.fatalError("Cannot handle cast with abstract types for now")

    case AsA(expr, ct) =>
      val fieldId = getUnionFieldFor(ct.clazz)
      val unionAccess = C.FieldAccess(rec(expr), TaggedUnion.value)
      C.FieldAccess(unionAccess, fieldId)

    case IntegralCast(expr0, newType0) =>
      val expr = rec(expr0)
      val newType = rec(PrimitiveType(newType0))
      C.Cast(expr, newType)

    case Lit(lit) => C.Lit(lit)

    case Ref(e) => C.Ref(rec(e))
    case Deref(e) => C.Deref(rec(e))

    case Return(e) => C.Return(rec(e))
    case Break => C.Break
  }

  // Construct an instantce of the given case class.
  //
  // There are three main cases:
  //  - 1) This case class has no parent;
  //  - 2) This class is part of a class hierarchy and some of the leaves classes have fields;
  //  - 3) This class is part of a class hierarchy but none of the concrete classes have fields.
  //
  // In the first case, we can "simply" construct the structure associated with this case class.
  //
  // In the second case, we need to construct the structure representing the class hierarchy with
  // its tag (an enumeration representing the runtime type of the object) and its value (an union
  // containing the relevant bits of data for the runtime type of the object).
  //
  // In the third and final case, we can express the whole class hierarchy using only an enumeration
  // to improve both memory space and execution speed.
  //
  // This function is just a proxy for the three main cases implementations.
  //
  // NOTE Empty classes are not supported in pure C99 (GNU-C99 does) so we have to add a dummy byte
  //      field. (This is how it is implemented in GCC.)
  //
  // NOTE For scenarios 2) we consider the whole class hierarchy even though in some contexts
  //      we could work with a subset. This leaves room for improvement, such as in the following
  //      (simplified) example:
  //
  //      abstract class GrandParent
  //      case class FirstChild(...) extends GrandParent
  //      abstract class Parent extends GrandParent
  //      case class GrandChildren1(...) extends Parent
  //      case class GrandChildren2(...) extends Parent
  //
  //      def foo(p: Parent) = ...
  //      def bar = foo(GrandChildren2(...))
  //
  //      In this example, `p` could hold information only about either GrandChildren1 or GrandChildren2
  //      but the current implementation will treat it as if were a GrandParent.
  //
  //      In order to implement such optimisation, we would need to keep track of which minimal "level"
  //      of the hierarchy is required. This might also involve playing around with the how methods
  //      are extracted wihtin Leon because a method defined on, say, Parent will be extracted as a
  //      function taking a GrandParent as parameter (with an extra pre-condition requiring that
  //      the parameter is an instance of Parent).
  //
  // NOTE Leon guarantees us that every abstract class has at least one (indirect) case class child.
  //
  private def constructObject(cd: ClassDef, args: Seq[Expr]): C.Expr = {
    require(!cd.isAbstract)

    // Mind the order of the cases w.r.t. the description above: they don't match.
    if (isEnumeration(cd))      enumerationConstruction(cd, args) // case n° 3
    else if (cd.parent.isEmpty) simpleConstruction(cd, args)      // case n° 1
    else                        hierarchyConstruction(cd, args)   // case n° 2
  }

  private def convertClass(cd: ClassDef): C.Type = {
    if (isEnumeration(cd)) getEnumFor(cd.hierarchyTop)
    else getStructFor(cd)
  }

  private def isEnumeration(cd: ClassDef): Boolean = {
    val leaves = cd.getHierarchyLeaves
    leaves forall { cd => cd.fields.isEmpty }
  }

  private val markedAsEmpty = MutableSet[ClassDef]()

  private def markAsEmpty(cd: ClassDef): Unit = {
    markedAsEmpty += cd
  }

  private def simpleConstruction(cd: ClassDef, args0: Seq[Expr]): C.StructInit = {
    // Ask for the C structure associated with cd
    val struct = getStructFor(cd)

    // Check whether an extra byte was added to the structure
    val args =
      if (markedAsEmpty(cd)) Seq(Lit(Int8Lit(0)))
      else args0

    C.StructInit(struct, args.map(rec(_)))
  }

  private def hierarchyConstruction(cd: ClassDef, args: Seq[Expr]): C.StructInit = {
    // Build the structure wrapper for tagged union
    val topStruct = getStructFor(cd.hierarchyTop)
    val union = getUnionFor(cd.hierarchyTop)
    val tag = getEnumLiteralFor(cd)
    val unionField = getUnionFieldFor(cd)
    val childInit = simpleConstruction(cd, args)
    val unionInit = C.UnionInit(union, unionField, childInit)

    C.StructInit(topStruct, Seq(tag, unionInit))
  }

  private def enumerationConstruction(cd: ClassDef, args: Seq[Expr]): C.EnumLiteral = {
    if (args.nonEmpty)
      ctx.reporter.fatalError("Enumeration should have no construction arguments!")

    getEnumLiteralFor(cd)
  }

  // Extract from cache, or build the C structure for the given class definition.
  //
  // Here are the three cases we can be in:
  //   1) the given class definition is a case class;
  //   2) it is the top class of a class hierarchy;
  //   3) it is an abstract class inside the class hierarchy.
  //
  // NOTE As described in a NOTE above, scenarios 2) & 3) are not yet distinguished.
  //      We currently treat case 3) as 2).
  private def getStructFor(cd: ClassDef): C.Struct = {
    val candidate = if (cd.isAbstract) cd.hierarchyTop else cd

    structCache get candidate match {
      case None =>
        val struct =
          if (candidate.isAbstract) buildStructForHierarchy(candidate)
          else buildStructForCaseClass(candidate)

        // Register the struct in the class cache AND as a datatype
        structCache.update(candidate, struct)
        register(struct)

        struct

      case Some(struct) => struct
    }
  }

  // Build the union used in the "tagged union" structure that is representing a class hierarchy.
  private def getUnionFor(cd: ClassDef): C.Union = unionCache.getOrElseUpdate(cd, {
    require(cd.isAbstract && cd.parent.isEmpty) // Top of hierarchy

    // List all (concrete) leaves of the class hierarchy as fields of the union.
    val leaves = cd.getHierarchyLeaves
    val fields = leaves.toSeq map { c => C.Var(getUnionFieldFor(c), getStructFor(c)) }
    val id = rec("union_" + cd.id)

    val union = C.Union(id, fields, cd.isExported)

    // Register the union as a datatype as well
    register(union)

    union
  })

  // Build the enum used in the "tagged union" structure that is representing a class hierarchy.
  private def getEnumFor(cd: ClassDef): C.Enum = enumCache.getOrElseUpdate(cd, {
    // List all (concrete) leaves of the class hierarchy as fields of the union.
    val leaves = cd.getHierarchyLeaves
    val literals = leaves.toSeq map getEnumLiteralFor
    val id = rec("enum_" + cd.id)

    C.Enum(id, literals)
  })

  // Get the tagged union field id for a leaf
  private def getUnionFieldFor(cd: ClassDef) = C.Id(cd.id + "_v")

  // Get the tag id for a leaf
  private def getEnumLiteralFor(cd: ClassDef) = C.EnumLiteral(C.Id("tag_" + cd.id))

  // Build a tagged union for the class hierarchy
  private def buildStructForHierarchy(top: ClassDef): C.Struct = {
    val tagType = getEnumFor(top)
    val tag = C.Var(TaggedUnion.tag, tagType)

    val unionType = getUnionFor(top)
    val union = C.Var(TaggedUnion.value, unionType)

    C.Struct(rec(top.id), tag :: union :: Nil, top.isExported, top.isPacked)
  }

  private def buildStructForCaseClass(cd: ClassDef): C.Struct = {
    // Here the mapping is straightforward: map the class fields,
    // possibly creating a dummy one to avoid empty classes.
    val fields = if (cd.fields.isEmpty) {
      ctx.reporter.warning(s"Empty structures are not allowed according to the C99 standard. " +
              s"I'm adding a dummy byte to ${cd.id} structure for compatibility purposes.")
      markAsEmpty(cd)
      Seq(C.Var(C.Id("extra"), C.Primitive(Int8Type)))
    } else cd.fields.map(rec(_))

    C.Struct(rec(cd.id), fields, cd.isExported, cd.isPacked)
  }

  private object TaggedUnion {
    val tag = C.Id("tag")
    val value = C.Id("value")
  }

  // Create a structure that will contain a data and length member to nicely wrap an array
  private def array2Struct(arrayType: ArrayType): C.Struct = arrayCache.getOrElseUpdate(arrayType, {
    val length = C.Var(Array.length, C.Primitive(Int32Type)) // Add const
    val base = rec(arrayType.base)
    val data = C.Var(Array.data, C.Pointer(base))
    val id = C.Id(repId(arrayType))

    val array = C.Struct(id, data :: length :: Nil, false, false)

    // This needs to get registered as a datatype as well
    register(array)

    array
  })

  private object Array {
    val length = C.Id("length")
    val data = C.Id("data")
  }

  // Helpers for == and != operators; create a CIR function if needed.
  // Such functions can use the == and != operators because the function
  // will need to be converted to C AST, recursively.
  //
  // TODO maybe it's more clever to move this earlier in the pipeline
  //      and benefit from other transformation...
  //
  // TODO currently, mutable object are taken by copy. This works
  //      because there is no side effect involved but this is not
  //      consistent with the rest. Is this an issue?
  //
  // NOTE In Leon, Any doesn't exists -> cannot override `equals`!
  // TODO When `equals` overriding is possible, add support for it.
  //
  // NOTE Leon doesn't support == on arrays.
  // TODO Such support should be added here as well one day.
  private object CmpFactory {
    private val cache = MutableMap[Type, FunDef]()

    import ir.PrimitiveTypes.{ StringType, BoolType }

    // Entry point of the factory
    def apply(typ: Type): FunVal = {
      cache.getOrElseUpdate(typ, {
        val fd = build(typ)

        // We need to register/traverse this function once. We do it here
        // because it's safe (not a recursive function). See comment in the
        // general rec(Expr) about FunVal.
        rec(fd)

        fd
      }).toVal
    }

    private def build(typ: Type): FunDef = {
      val id = "equals_" + repId(typ)
      val retTyp = PrimitiveType(BoolType)

      val lhsVd = ValDef("lhs", typ, isVar = false)
      val rhsVd = ValDef("rhs", typ, isVar = false)
      val params = Seq(lhsVd, rhsVd)

      val lhs = Binding(lhsVd)
      val rhs = Binding(rhsVd)

      val body = typ match {
        case PrimitiveType(StringType) => buildStringCmpBody()
        case ClassType(cd) => buildClassCmpBody(cd, lhs, rhs)
        case typ => ctx.reporter.fatalError(s"Unexpected type $typ in CmpFactory!")
      }

      FunDef(id, retTyp, Seq(), params, body, false, true)
    }

    private def buildStringCmpBody() = FunBodyManual(
      headerIncludes = Seq("string.h"),
      cIncludes = Seq(),
      body =
        """|bool __FUNCTION__(char* lhs, char* rhs) {
           |  return strcmp(lhs, rhs) == 0;
           |}
           |""".stripMargin
    )

    // Compare one after the other each class member, if they have the same runtime type.
    private def buildClassCmpBody(cd: ClassDef, lhs: Binding, rhs: Binding): FunBodyAST = {
      val result =
        if (cd.getFullHierarchy.size == 1) buildLeafClassCmpBody(cd, lhs, rhs)
        else {
          val subs = cd.getHierarchyLeaves map { leaf =>
            val ct = ClassType(leaf)
            val typeTest = foldAnd(IsA(lhs, ct) :: IsA(rhs, ct) :: Nil)
            val lhs2 = AsA(lhs, ct)
            val rhs2 = AsA(rhs, ct)
            val fieldsTest = buildLeafClassCmpBody(leaf, lhs2, rhs2)
            foldAnd(typeTest :: fieldsTest :: Nil)
          }

          foldOr(subs.toList) // needs to be equal to one sub test
        }

      FunBodyAST(Return(result))
    }

    private def fold(op: BinaryOperator, default: Expr)(exprs: List[Expr]): Expr = exprs match {
      case Nil => default
      case expr :: Nil => expr
      case first :: second :: Nil => BinOp(op, first, second)
      case head :: tail => BinOp(op, head, foldAnd(tail))
    }

    private def foldAnd = fold(And, Lit(BoolLit(true))) _
    private def foldOr = fold(Or, Lit(BoolLit(false))) _

    private def buildLeafClassCmpBody(cd: ClassDef, lhs: Expr, rhs: Expr): Expr = {
      assert(lhs.getType == rhs.getType && ClassType(cd) == lhs.getType && cd.getDirectChildren.isEmpty)

      // Checks that all fields are equals
      val subs = cd.fields map { case ValDef(field, typ, _) =>
        assert(!typ.isReference)
        val accessL = FieldAccess(lhs, field)
        val accessR = FieldAccess(rhs, field)
        BinOp(Equals, accessL, accessR)
      }

      foldAnd(subs.toList)
    }
  }

}
