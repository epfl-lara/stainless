/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen
package codegen

import stainless.Identifier
import intermediate.{trees => t}
import wasm.{GlobalsHandler, LocalsHandler}
import wasm.Expressions.{eq => EQ, _}
import wasm.Types._
import wasm.Definitions._

/** Implements memory allocations in linear memory
  *
  * Global variable 0 points to the free linear memory boundary
  *
  */
object LinearMemoryCodeGen extends CodeGeneration {
  private val memB = "memB"
  private val safeMem: Boolean = true
  private val mallocName = "_malloc_"
  // Checks if we can allocate a given number of bytes in memory.
  // If not, tries to grow the memory and fails if it is impossible.
  // Then allocates bytes and returns the **previous** free memory boundary
  private def mkMalloc(implicit funEnv: FunEnv) = {
    val pageShift = I32Const(16) // 64K
    FunDef(mallocName, Seq(ValDef("size", i32)), i32) { implicit lh =>
      implicit val env = funEnv.env(lh)
      implicit val gh = env.gh
      val getMem = GetGlobal(memB)
      val size = GetLocal("size")
      val loop = freshLabel("loop")
      Sequence(Seq(Loop(loop,
        If(
          freshLabel("label"),
          gt(Unsigned)(
            add(getMem, size),
            shl(MemorySize, pageShift)
          ),
          If(
            freshLabel("label"),
            EQ(MemoryGrow(MemorySize), I32Const(-1)),
            Sequence(Seq(
              transform(t.Output(t.StringLiteral("Error: Out of memory"))),
              Unreachable
            )),
            Br(loop)
          ),
          Return(Sequence(Seq(
            getMem,
            SetGlobal(memB, add(getMem, size))
          )))
        )
      ), I32Const(0))) // bogus, to satisfy the type checker
    }
  }
  private def malloc(size: Expr)(implicit gh: GlobalsHandler) = {
    if (safeMem) Call(mallocName, i32, Seq(size))
    else Sequence(Seq(
      GetGlobal(memB),
      SetGlobal(memB, add(GetGlobal(memB), size))
    ))
  }

  override protected def mkImports(s: t.Symbols): Seq[Import] =
    Import("system", "mem", Memory(1)) +: super.mkImports(s)

  protected def mkGlobals(s: t.Symbols) = Seq(ValDef(memB, i32))

  protected def updateGlobals(funEnv: FunEnv): Unit = {
    funEnv.gh.update(memB, I32Const(funEnv.dh.nextFree))
  }

  override def mkBuiltins(s: t.Symbols, toExecute: Seq[Identifier])(implicit funEnv: FunEnv): Seq[FunDef] = {
    super.mkBuiltins(s, toExecute) ++ (if (safeMem) Seq(mkMalloc) else Seq())
  }

  /* Helpers */
  // Compute the address of an element in an array from base and offset
  private def elemAddr(array: Expr, offset: Expr) = add(array, mul(add(offset, I32Const(1)), I32Const(4)))
  private def strCharAddr(string: Expr, offset: Expr) = add(string, add(offset, I32Const(4)))
  private def unbox(tpe: Type, ref: Expr) = Load(tpe, None, add(ref, I32Const(4)))

  protected def mkEquality(s: t.Symbols): FunDef = {
    implicit val impS = s

    def boxedEq(tpe: Type, lhs: Expr, rhs: Expr)(name: String = tpe.toString): (Expr, String) =
      (EQ(unbox(tpe, lhs), unbox(tpe, rhs)), name)

    def recordEq(rec: t.RecordSort, lhs: Expr, rhs: Expr): (Expr, String) = {
      // We get offsets of all fields except first (typeTag) which we know is equal already
      val offsets = rec.allFields.scanLeft(0)((off, fld) => off + transform(fld.getType).size).tail
      val fieldEqs = rec.allFields.tail.zip(offsets).map { case (fld, off) =>
        val wasmTpe = transform(fld.getType)
        val l = Load(wasmTpe, None, add(lhs, I32Const(off)))
        val r = Load(wasmTpe, None, add(rhs, I32Const(off)))
        surfaceEq(l, r, fld.getType)
      }
      (fieldEqs.foldRight(I32Const(1): Expr) { case (e, rest) =>
        If(freshLabel("label"), e, rest, I32Const(0))
      }, rec.id.uniqueName)
    }

    def allEqs(lhs: Expr, rhs: Expr): Seq[(Expr, String)] = {
      Seq(
        (I32Const(1), "unit"),
        boxedEq(i32, lhs, rhs)("boolean"),
        boxedEq(i32, lhs, rhs)("char"),
        boxedEq(i32, lhs, rhs)(),
        boxedEq(i64, lhs, rhs)(),
        boxedEq(i64, lhs, rhs)("BigInt"),
        boxedEq(f64, lhs, rhs)(),
        boxedEq(i32, lhs, rhs)("array"),
        boxedEq(i32, lhs, rhs)("string"),
        boxedEq(i32, lhs, rhs)("function")
      ) ++ {
        val sorts = s.records.values.toSeq.collect { case c: t.ConstructorSort => c }.sortBy(_.typeTag)
        sorts map (s => recordEq(s, lhs, rhs))
      }
    }

    FunDef(refEqualityName, Seq(ValDef("lhs", i32), ValDef("rhs", i32)), i32) { implicit lh =>
      Sequence(Seq(
        If(
          freshLabel("label"),
          EQ(Load(i32, None, GetLocal("lhs")), Load(i32, None, GetLocal("rhs"))), {
            val eqs = allEqs(GetLocal("lhs"), GetLocal("rhs"))
            // We use i32 as default, whatever, should not happen
            val jump = BrTable(eqs.map(_._2), eqs.head._2, Load(i32, None, GetLocal("lhs")), None)
            eqs.foldLeft(jump: Expr) { case (first, (equality, label)) =>
              Sequence(Seq(Block(label, first), Return(equality)))
            }
          },
          Return(I32Const(0))
        ),
        I32Const(0)
      ))
    }
  }

  protected def mkInequality(s: t.Symbols): FunDef = {
    implicit val impS = s

    def boxedIneq(tpe: Type, lhs: Expr, rhs: Expr)(name: String = tpe.toString): (Expr, String) =
      (baseTypeIneq(unbox(tpe, lhs), unbox(tpe, rhs)), name)

    def recordIneq(rec: t.RecordSort, lhs: Expr, rhs: Expr, temp: String)(implicit lh: LocalsHandler): (Expr, String) = {
      // We get offsets of all fields except first (typeTag) which we know is equal already
      val offsets = rec.allFields.scanLeft(0)((off, fld) => off + transform(fld.getType).size).tail
      val fieldIneqs = rec.allFields.tail.zip(offsets).map { case (fld, off) =>
        val wasmTpe = transform(fld.getType)
        val l = Load(wasmTpe, None, add(lhs, I32Const(off)))
        val r = Load(wasmTpe, None, add(rhs, I32Const(off)))
        surfaceIneq(l, r, fld.getType)
      }
      (fieldIneqs.foldRight(I32Const(0): Expr) { case (e, rest) =>
        Sequence(Seq(
          SetLocal(temp, e),
          If(freshLabel("label"), eqz(GetLocal(temp)), rest, GetLocal(temp))
        ))
      }, rec.id.uniqueName)
    }

    def allIneqs(lhs: Expr, rhs: Expr, temp: String)(implicit lh: LocalsHandler): Seq[(Expr, String)] = {
      Seq(
        (I32Const(0), "unit"),
        boxedIneq(i32, lhs, rhs)("boolean"),
        boxedIneq(i32, lhs, rhs)("char"),
        boxedIneq(i32, lhs, rhs)(),
        boxedIneq(i64, lhs, rhs)(),
        boxedIneq(i64, lhs, rhs)("BigInt"),
        boxedIneq(f64, lhs, rhs)(),
        boxedIneq(i32, lhs, rhs)("array"),
        boxedIneq(i32, lhs, rhs)("string"),
        boxedIneq(i32, lhs, rhs)("function")
      ) ++ {
        val sorts = s.records.values.toSeq.collect { case c: t.ConstructorSort => c }.sortBy(_.typeTag)
        sorts map (s => recordIneq(s, lhs, rhs, temp))
      }
    }

    FunDef(refInequalityName, Seq(ValDef("lhs", i32), ValDef("rhs", i32)), i32) { implicit lh =>
      val temp = lh.getFreshLocal("temp", i32)
      lh.getFreshLocal("tempf32", f32)
      lh.getFreshLocal("tempf64", f64)
      Sequence(Seq(
        SetLocal(temp, sub(Load(i32, None, GetLocal("lhs")), Load(i32, None, GetLocal("rhs")))),
        If(
          freshLabel("label"),
          eqz(GetLocal(temp)), {
            val ineqs = allIneqs(GetLocal("lhs"), GetLocal("rhs"), temp)
            // We use i32 as default, whatever, should not happen
            val jump = BrTable(ineqs.map(_._2), ineqs.head._2, Load(i32, None, GetLocal("lhs")), None)
            ineqs.foldLeft(jump: Expr) { case (first, (ineq, label)) =>
              Sequence(Seq(Block(label, first), Return(ineq)))
            }
          },
          Return(GetLocal(temp))
        ),
        I32Const(0) // Should never happen
      ))
    }
  }


  protected def mkToString(s: t.Symbols)(implicit funEnv: FunEnv): FunDef = {

    def boxedToString(tpe: Type, arg: Expr)(tpeName: String = tpe.toString): (Expr, String) =
      (Call(toStringName(tpeName), i32, Seq(unbox(tpe, arg))), tpeName)

    def recordToString(rec: t.ConstructorSort, arg: Expr): (Expr, String) = {
      (Call(toStringName(rec.id.uniqueName), i32, Seq(arg)), rec.id.uniqueName)
    }

    def allToStrings(arg: Expr): Seq[(Expr, String)] = {
      Seq(
        (Call(toStringName("unit"), i32, Seq()), "unit"),
        boxedToString(i32, arg)("boolean"),
        boxedToString(i32, arg)("char"),
        boxedToString(i32, arg)(),
        boxedToString(i64, arg)(),
        boxedToString(i64, arg)("BigInt"),
        boxedToString(f64, arg)(),
        boxedToString(i32, arg)("array"),
        (unbox(i32, arg), "string"),
        (Call(toStringName("fun"), i32, Seq()), "function")
      ) ++ {
        val sorts = s.records.values.toSeq.collect { case c: t.ConstructorSort => c }.sortBy(_.typeTag)
        sorts map (s => recordToString(s, arg))
      }
    }

    FunDef(refToStringName, Seq(ValDef("arg", i32)), i32) { implicit lh =>
      val toStrings = allToStrings(GetLocal("arg"))
      // We use i32 as default, whatever, should not happen
      val jump = BrTable(toStrings.map(_._2), toStrings(2)._2, Load(i32, None, GetLocal("arg")), None)
      toStrings.foldLeft(jump: Expr) { case (first, (toS, label)) =>
        Sequence(Seq(Block(label, first), Return(toS)))
      }
    }
  }

  protected val builtinToStrings = Set("char", "array", "BigInt")

  protected def mkCharToString(implicit funEnv: FunEnv): FunDef = {
    implicit val gh = funEnv.gh
    FunDef(toStringName("char"), Seq(ValDef("arg", i32)), i32){ implicit lh =>
      val mem = lh.getFreshLocal("mem", i32)
      Sequence(Seq(
        SetLocal(mem, malloc(I32Const(8))),
        Store(None, GetLocal(mem), I32Const(1)),
        Store(None, add(GetLocal(mem), I32Const(4)), GetLocal("arg")),
        GetLocal(mem)
      ))
    }
  }

  protected def mkBigIntToString(implicit funEnv: FunEnv): FunDef = {
    FunDef(toStringName("BigInt"), Seq(ValDef("arg", i64)), i32){ implicit lh =>
      implicit val env = funEnv.env(lh)
      Call(stringConcatName, i32, Seq(
        Call(stringConcatName, i32, Seq(
          transform(t.StringLiteral("BigInt(")),
          Call(toStringName("i64"), i32, Seq(GetLocal("arg")))
        )),
        transform(t.StringLiteral(")"))
      ))
    }
  }

  protected def mkArrayToString(implicit funEnv: FunEnv): FunDef = {
    FunDef(toStringName("array"), Seq(ValDef("array", i32)), i32) { implicit lh =>
      implicit val env = funEnv.env(lh)
      val ind = lh.getFreshLocal(freshLabel("index"), i32)
      val curr = lh.getFreshLocal(freshLabel("current"), i32)
      val loop = freshLabel("loop")

      def indToPtr(e: Expr) = elemAddr(GetLocal("array"), e)

      Sequence(Seq(
        SetLocal(ind, I32Const(0)),
        SetLocal(curr, transform(t.StringLiteral(""))),
        Loop(loop,
          If(
            freshLabel("label"),
            lt(Unsigned)(GetLocal(ind), Load(i32, None, GetLocal("array"))),
            Sequence(Seq(
              SetLocal(curr,
                Call(stringConcatName, i32, Seq(
                  GetLocal(curr),
                  If(
                    freshLabel("label"),
                    eqz(GetLocal(ind)),
                    Call(refToStringName, i32, Seq(Load(i32, None, indToPtr(GetLocal(ind))))),
                    Call(stringConcatName, i32, Seq(
                      transform(t.StringLiteral(", ")),
                      Call(refToStringName, i32, Seq(Load(i32, None, indToPtr(GetLocal(ind)))))
                    ))
                  )
                ))
              ),
              SetLocal(ind, add(GetLocal(ind), I32Const(1))),
              Br(loop)
            )),
            Nop
          )
        ),
        Call(stringConcatName, i32, Seq(
          transform(t.StringLiteral("Array(")),
          Call(stringConcatName, i32, Seq(
            GetLocal(curr), transform(t.StringLiteral(")"))
          ))
        ))
      ))
    }
  }

  protected def mkStringLiteral(str: String)(implicit env: Env): Expr = {
    val length = str.length
    val mask = 0xFF
    val l0 = length & mask
    val l1 = (length >> 8) & mask
    val l2 = (length >> 16) & mask
    val l3 = (length >> 24) & mask
    val lbytes = Seq(l0, l1, l2, l3).map(_.toByte.r) // Little endian
    val content = str.map(_.toByte.f)
    I32Const(env.dh.addNext(lbytes ++ content))
  }

  protected def mkSubstring(implicit funEnv: FunEnv): FunDef = {
    implicit val gh = funEnv.gh
    FunDef(substringName, Seq("string", "from", "to").map(ValDef(_, i32)), i32) { implicit lh =>
      val str = GetLocal("string")
      val from = GetLocal("from")
      val to = GetLocal("to")
      val index = lh.getFreshLocal("index", i32)
      val length = lh.getFreshLocal("length", i32)
      val loop = freshLabel("loop")
      val mem = lh.getFreshLocal("mem", i32)
      Sequence(Seq(
        SetLocal(length, sub(to, from)),
        SetLocal(mem, malloc(add(GetLocal(length), I32Const(4)))),
        Store(None, GetLocal(mem), GetLocal(length)),
        SetLocal(index, I32Const(0)),
        Loop(loop,
          If(
            freshLabel("label"),
            lt(Unsigned)(GetLocal(index), GetLocal(length)), // index < length
            Sequence(Seq(
              Store(Some(i8),
                strCharAddr(GetLocal(mem), GetLocal(index)),
                Load(i32, Some((i8, Unsigned)), strCharAddr(str, add(from, GetLocal(index))))
              ),
              SetLocal(index, add(GetLocal(index), I32Const(1))),
              Br(loop)
            )),
            Nop
          )
        ),
        GetLocal(mem)
      ))
    }
  }

  protected def mkStringConcat(implicit funEnv: FunEnv): FunDef = {
    implicit val gh = funEnv.gh
    FunDef(stringConcatName, Seq("lhs", "rhs").map(ValDef(_, i32)), i32) { implicit lh =>
      val lhs = GetLocal("lhs")
      val rhs = GetLocal("rhs")
      val len1 = Load(i32, None, lhs)
      val len2 = Load(i32, None, rhs)
      val index = lh.getFreshLocal("index", i32)
      val mem = lh.getFreshLocal("mem", i32)
      val loop = freshLabel("loop")
      Sequence(Seq(
        SetLocal(mem, malloc(add(add(len1, len2), I32Const(4)))),
        Store(None, GetLocal(mem), add(len1, len2)), // concat length
        SetLocal(index, I32Const(0)),
        Loop(loop,
          If(
            freshLabel("label"),
            lt(Signed)(GetLocal(index), len1), // index < length
            Sequence(Seq(
              Store(Some(i8),
                strCharAddr(GetLocal(mem), GetLocal(index)),
                Load(i32, Some((i8, Unsigned)), strCharAddr(lhs, GetLocal(index)))
              ),
              SetLocal(index, add(GetLocal(index), I32Const(1))),
              Br(loop)
            )),
            Nop
          )
        ),
        SetLocal(index, I32Const(0)),
        Loop(loop,
          If(
            freshLabel("label"),
            lt(Signed)(GetLocal(index), len2), // index < length
            Sequence(Seq(
              Store(Some(i8),
                strCharAddr(GetLocal(mem), add(len1, GetLocal(index))),
                Load(i32, Some((i8, Unsigned)), strCharAddr(rhs, GetLocal(index)))
              ),
              SetLocal(index, add(GetLocal(index), I32Const(1))),
              Br(loop)
            )),
            Nop
          )
        ),
        GetLocal(mem)
      ))
    }
  }

  protected def mkRecord(recordType: t.RecordType, fields: Seq[Expr])(implicit env: Env): Expr = {
    implicit val gh = env.gh
    implicit val lh = env.lh
    // offsets for fields, with last element being the new memory boundary
    val offsets = fields.scanLeft(0)(_ + _.getType.size)
    val mem = lh.getFreshLocal(freshLabel("mem"), i32)

    val mkFields = fields.zip(offsets).map { case (e, off) =>
      if (e.getType == void) e
      else Store(None, add(GetLocal(mem), I32Const(off)), e)
    }

    Sequence(
      SetLocal(mem, malloc(I32Const(offsets.last))) +:
      mkFields :+
      GetLocal(mem)
    )
  }

  protected def mkRecordSelector(expr: Expr, rt: t.RecordType, id: Identifier)(implicit env: Env): Expr = {
    implicit val s = env.s
    val fields = rt.getRecord.allFields
    val tpe = transform(fields.find(_.id == id).get.getType)
    if (tpe == void) Nop
    else {
      val offset = fields
        .takeWhile(_.id != id)
        .map(fd => transform(fd.getType).size)
        .sum
      Load(tpe, None, add(expr, I32Const(offset)))
    }
  }

  protected def mkCastDown(expr: Expr, subType: t.RecordType)(implicit env: Env): Expr = {
    expr
  }

  // Up-casts are trivial
  protected def mkCastUp(expr: Expr, superType: t.RecordType)(implicit env: Env): Expr = expr

  protected def mkNewArray(length: Expr, init: Option[Expr])(implicit env: Env): Expr = {
    implicit val lh = env.lh
    implicit val gh = env.gh
    val evLength = lh.getFreshLocal(freshLabel("length"), i32)
    val evInit = lh.getFreshLocal(freshLabel("init"), i32)
    val mem = lh.getFreshLocal("mem", i32)

    Sequence(
      Seq(
        SetLocal(evLength, length),
        SetLocal(mem, malloc(mul(add(GetLocal(evLength), I32Const(1)), I32Const(4)))),
        Store(None, GetLocal(mem), GetLocal(evLength))
      ) ++
      init.toSeq.flatMap { elem =>
        val ind = lh.getFreshLocal(freshLabel("index"), i32)
        val loop = freshLabel("loop")
        Seq(
          SetLocal(evInit, elem),
          SetLocal(ind, I32Const(0)),
          Loop(loop, Sequence(Seq(
            If(
              freshLabel("label"),
              lt(Signed)(GetLocal(ind), GetLocal(evLength)),
              Sequence(Seq(
                Store(None,
                  elemAddr(GetLocal(mem), GetLocal(ind)),
                  GetLocal(evInit)
                ),
                SetLocal(ind, add(GetLocal(ind), I32Const(1))),
                Br(loop)
              )),
              Nop
            )
          )))
        )
      } ++
      Seq(GetLocal(mem))
    )
  }

  protected def mkArrayGet(array: Expr, index: Expr)(implicit env: Env): Expr = {
    Load(i32, None, elemAddr(array, index))
  }

  protected def mkArraySet(array: Expr, index: Expr, value: Expr)(implicit env: Env): Expr = {
    Store(None, elemAddr(array, index), value)
  }

  protected def mkArrayLength(expr: Expr)(implicit env: Env): Expr = Load(i32, None, expr)

  override def transform(tpe: t.Type)(implicit s: t.Symbols): Type = tpe match {
    case t.ArrayType(_) | t.RecordType(_) | t.StringType() => i32
    case _ => super.transform(tpe)
  }
}
