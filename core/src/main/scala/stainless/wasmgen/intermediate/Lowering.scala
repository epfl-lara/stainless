/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen
package intermediate

import inox.Context
import stainless.ast.SymbolIdentifier
import stainless.{FreshIdentifier, Identifier}

trait Lowerer extends stainless.transformers.Transformer {
  val s = stainless.trees
  val t = trees

  case class Env(syms: s.Symbols, manager: SymbolsManager, generateChecks: Boolean)

  protected val lib: LibProvider { val trees: s.type } = new LibProvider {
    protected val trees: s.type = s
  }

  override def transform(tp: s.Type, env: Env): t.Type = {
    implicit val impSyms: s.Symbols = env.syms
    import t._
    tp match {
      case s.ADTType(id, tps) =>
        RecordType(id)

      case s.FunctionType(from, to) =>
        RecordType(env.manager.funPointerSort(
          FunctionType(Seq.fill(from.size)(AnyRefType), AnyRefType)
        ))

      case s.TupleType(bases) =>
        RecordType(lib.sort(s"Tuple${bases.size}").id)
      case s.SetType(_) =>
        RecordType(lib.sort("Set").id)
      case s.BagType(_) =>
        RecordType(lib.sort("Bag").id)
      case s.MapType(_, _)  =>
        RecordType(lib.sort("Map").id)

      case s.PiType(params, to) =>
        transform(s.FunctionType(params.map(_.getType), to.getType), env)
      case s.SigmaType(params, to) =>
        transform(s.TupleType(params.map(_.getType) :+ to.getType), env)
      case s.RefinementType(vd, prop) =>
        transform(vd.getType, env)

      case s.TypeParameter(id, flags) => // Type erasure
        RecordType(AnyRefSort.id)

      case s.ArrayType(base) =>
        ArrayType(AnyRefType)

      case _ =>
        // Base types, functions and strings
        super.transform(tp, env)
    }
  }
}

private[wasmgen] class SymbolsManager {
  import trees._
  import scala.collection.mutable.{Map => MMap}

  private val functions_ : MMap[Identifier, FunDef] = MMap()
  private val records_ : MMap[Identifier, RecordSort] = MMap()
  private val boxedSorts: MMap[Type, Identifier] = MMap()
  private val funRecords: MMap[FunctionType, Identifier] = MMap()

  def addFunction(fd: FunDef): Unit = functions_ += fd.id -> fd

  def funPointerSort(ft: FunctionType): Identifier =
    funRecords.getOrElseUpdate(ft, {
      val fr = new FunPointerSort(FreshIdentifier("`" + ft.asString(PrinterOptions()) + "`"), ft)
      records_ += fr.id -> fr
      fr.id
    })

  def closureSort(funType: FunctionType, env: Seq[ValDef]): Identifier = {
    // Always make a new closure sort
    val cs = new ClosureSort(funPointerSort(funType), env)
    records_ += cs.id -> cs
    cs.id
  }

  def boxedSort(tpe: Type): Identifier = boxedSorts.getOrElseUpdate(tpe, {
    val s = new BoxedSort(tpe)
    records_ += s.id -> s
    s.id
  })

  def functions = functions_
  def records = records_
}


private [wasmgen] class ExprLowerer(
  manager: SymbolsManager,
  sym0: stainless.trees.Symbols,
  initSorts: Map[Identifier, trees.RecordSort],
  context: Context
) extends Lowerer {
  import t._
  def initEnv = Env(sym0, manager, true)

  private def isRecordType(tpe: t.Type) = tpe match {
    case t.RecordType(_) => true
    case _ => false
  }

  private def maybeBox(e: s.Expr, expected: t.Type, env: Env): t.Expr = {
    implicit val impSyms = env.syms
    val trType = transform(e.getType, env)
    val trE = transform(e, env)
    if (!isRecordType(trType) && expected == AnyRefType)
      CastUp(
        Record(
          RecordType(env.manager.boxedSort(trType)),
          Seq(Int32Literal(typeToTag(trType)), trE)),
        AnyRefType
      )
    else if (trType == expected) trE
    else CastUp(trE, AnyRefType)
  }
  private def maybeUnbox(e: t.Expr, real: t.Type, expected: t.Type, env: Env): t.Expr = {
    implicit val impSyms = env.syms
    if (!isRecordType(expected) && real == AnyRefType)
      RecordSelector(
        CastDown(e, RecordType(manager.boxedSort(expected))),
        boxedValueId
      )
    else if (real == expected) e
    else CastDown(e, expected.asInstanceOf[RecordType])
  }

  def transform(fd: s.FunDef): t.FunDef = {
    new t.FunDef(
      transform(fd.id, initEnv),
      Seq(),
      fd.params map (transform(_, initEnv)),
      transform(fd.returnType, initEnv),
      transform(fd.fullBody, initEnv),
      fd.flags map (transform(_, initEnv))
    ).copiedFrom(fd)
  }

  override def transform(e: s.Expr, env: Env): Expr = {
    implicit val impSyms = env.syms
    val generateChecks = env.generateChecks

    def inBounds(array: t.Expr, index: t.Expr) = {
      And(
        GreaterEquals(index, Int32Literal(0)),
        LessThan(index, ArrayLength(array))
      )
    }

    e match {
      // Misc.
      case s.Annotated(body, flags) if flags contains s.Unchecked =>
        // Unchecked flag suppresses checks
        transform(body, env.copy(generateChecks = false))
      case s.Annotated(body, _) =>
        transform(body, env)
      case s.Error(tpe, description) =>
        Sequence(Seq(
          Output(transform(s.StringLiteral(description), env)),
          NoTree(transform(tpe, env))
        ))

      // Contracts
      case s.Assume(pred, body) =>
        if (generateChecks)
          IfExpr(transform(pred, env), transform(body, env), NoTree(transform(body.getType, env)))
        else
          transform(body, env)
      case s.Require(pred, body) =>
        transform(s.Assume(pred, body), env)
      case s.Ensuring(body, s.Lambda(Seq(vd), lbody)) =>
        if (generateChecks) {
          val trV = transform(vd, env)
          Let(trV, transform(body, env),
            IfExpr(transform(lbody, env), trV.toVariable, NoTree(trV.tpe))
          )
        } else {
          transform(body, env)
        }
      case s.Assert(pred, error, body) =>
        if (generateChecks)
          IfExpr(
            transform(pred, env),
            transform(body, env),
            transform(s.Error(body.getType, error getOrElse ""), env)
          )
        else transform(body, env)

      // Higher-order
      case s.Application(callee, args) =>
        val tCallee = transform(callee, env)
        val vCallee = Variable.fresh("fun", transform(callee.getType, env))
        // All arguments are passed to lambdas and result is returned as anyref
        Let(vCallee.toVal, tCallee,
          maybeUnbox(Application(
            RecordSelector(vCallee, funPointerId),
            vCallee +: args.map( arg => maybeBox(arg, AnyRefType, env))
          ), AnyRefType, transform(e.getType, env), env)
        )
      case s.Lambda(params, body) =>
        val boxedFunType = FunctionType(
          Seq.fill(params.size)(AnyRefType),
          AnyRefType
        )
        val fv = (s.exprOps.variablesOf(body).map(_.toVal) -- params).toSeq.map(transform(_, env))

        // Make/find a RecordSort for this function type, and one with the specific env.
        val funRecId = manager.funPointerSort(boxedFunType)

        val freshEnv = fv.map(_.freshen)
        val closureSortId = manager.closureSort(boxedFunType, freshEnv)

        val funRecordType = RecordType(funRecId)
        val closureType = RecordType(closureSortId)

        val function = {
          def extractEnv(env: Variable, body: Expr) = {
            val castEnv = ValDef.fresh("env", closureType)
            Let(
              castEnv,
              CastDown(env, closureType),
              fv.zip(freshEnv).foldRight(body) { case ((v, envId), rest) =>
                Let(v, RecordSelector(castEnv.toVariable, envId.id), rest)
              }
            )
          }

          def unboxParams(boxedParams: Seq[ValDef], body: Expr) = {
            boxedParams.zip(params).foldRight(body) { case ((boxed, unboxed), rest) =>
              Let(transform(unboxed, env),
                maybeUnbox(boxed.toVariable, AnyRefType, transform(unboxed.getType, env), env),
                rest
              )
            }
          }

          def boxResult(body: s.Expr) = maybeBox(body, AnyRefType, env)

          val fd = {
            val envParam  = ValDef.fresh("env", funRecordType)
            val boxedParams = params map (p => ValDef(p.id.freshen, AnyRefType))
            new FunDef(
              FreshIdentifier("lambda"), Seq(),
              envParam +: boxedParams,
              AnyRefType,
              extractEnv(
                envParam.toVariable,
                unboxParams(
                  boxedParams,
                  boxResult(body))),
              Seq(Dynamic)
            )
          }

          manager.addFunction(fd)
          fd
        }

        val closure = {
          CastUp(
            Record(
              closureType,
              Int32Literal(typeToTag(boxedFunType)) +: FunctionPointer(function.id) +: fv.map(_.toVariable)
            ),
            funRecordType
          )
        }

        closure

      // Booleans
      case s.Implies(lhs, rhs) => transform(s.Or(lhs, s.Not(rhs)), env)

      // ADTs
      case me: s.MatchExpr =>
        transform(impSyms.matchToIfThenElse(me, assumeExhaustive = !generateChecks), env)
      case adt@s.ADT(id, tps, args) =>
        // Except constructor fields, we also store the i32 tag corresponding to this constructor
        val typeTag = initSorts(id).asInstanceOf[ConstructorSort].typeTag
        val formals = sym0.constructors(id).fields.map(_.getType)
        val tpe = RecordType(id)
        val parentType = RecordType(sym0.constructors(id).sort)
        val invariant = adt.getConstructor.sort.invariant
        val withoutInv = CastUp(
          Record(tpe, Int32Literal(typeTag) +: args.zip(formals).map {
            case (arg, formal) => maybeBox(arg, transform(formal, env), env)
          }),
          parentType
        )
        invariant match {
          case Some(inv) if generateChecks =>
            val binder = ValDef(FreshIdentifier(id.name.toLowerCase), parentType)
            Let(
              binder, withoutInv,
              IfExpr(
                FunctionInvocation(inv.id, Seq(), Seq(binder.toVariable)),
                binder.toVariable,
                transform(s.Error(adt.getType, s"Error: Invariant failed for ${adt.getConstructor.sort.id}"), env))
            )
          case _ =>
            withoutInv
        }
      case s.IsConstructor(expr, id) =>
        // We need to compare the constructor code of given value
        // to the code corresponding to constructor 'id'
        Equals(
          RecordSelector(transform(expr, env), typeTagID),
          Int32Literal(initSorts(id).asInstanceOf[ConstructorSort].typeTag)
        )
      case as@s.ADTSelector(adt, selector) =>
        val s.ADTType(parent, _) = adt.getType
        val (childId, formalType) = (for {
          ch <- initSorts.values
          if ch.parent.contains(parent)
          fd <- ch.fields
          if fd.id == selector
        } yield (ch.id, fd.tpe)).head
        if (generateChecks) {
          val binder = ValDef(FreshIdentifier(childId.name.toLowerCase), RecordType(parent))
          Let(binder, transform(adt, env),
            IfExpr(
              Equals(
                RecordSelector(binder.toVariable, typeTagID),
                Int32Literal(initSorts(childId).asInstanceOf[ConstructorSort].typeTag)
              ),
              maybeUnbox(
                RecordSelector(
                  CastDown(binder.toVariable, RecordType(childId)),
                  selector
                ),
                formalType,
                transform(as.getType, env),
                env
              ),
              transform(s.Error(as.getType, s"Error: Cannot cast to ${childId.name}"), env) ) )
        } else {
          maybeUnbox(
            RecordSelector(
              CastDown(transform(adt, env), RecordType(childId)),
              selector
            ),
            formalType,
            transform(as.getType, env),
            env
          )
        }

      case s.FunctionInvocation(id, tps, args) =>
        val formals = sym0.functions(id).params.map(_.getType)
        maybeUnbox(
          FunctionInvocation(id, Seq(),
            args zip formals map { case (arg, formal) =>
              maybeBox(arg, transform(formal, env), env)
            }
          ),
          transform(sym0.functions(id).returnType, env),
          transform(e.getType, env),
          env
        )

      // Arrays
      case s.FiniteArray(elems, base) =>
        val arr = Variable.fresh("array", ArrayType(AnyRefType))
        Let(arr.toVal,
          NewArray(Int32Literal(elems.length), None),
          sequence(elems.zipWithIndex.map { case (elem, index) =>
            ArraySet(arr, Int32Literal(index), maybeBox(elem, AnyRefType, env))
          } :+ arr)
        )
      case s.LargeArray(elems, default, size, base) =>
        val arr = Variable.fresh("array", ArrayType(AnyRefType))
        Let(arr.toVal,
          NewArray(transform(size, env), Some(maybeBox(default, AnyRefType, env))),
          sequence( elems.toSeq.sortBy(_._1).map { case (index, elem) =>
            ArraySet(arr, Int32Literal(index), maybeBox(elem, AnyRefType, env))
          } :+ arr)
        )
      case s.ArrayUpdated(array, index, value) =>
        // TODO: Copy functional arrays or analyze when we don't need to do so
        val arr = Variable.fresh("array", ArrayType(AnyRefType))
        if (generateChecks) {
          val ind = Variable.fresh("index", Int32Type())
          Let(arr.toVal, transform(array, env),
            Let(ind.toVal, transform(index, env),
              IfExpr(
                inBounds(arr, ind),
                Sequence(Seq(
                  ArraySet(arr, ind, maybeBox(value, AnyRefType, env)),
                  arr
                )),
                transform(s.Error(array.getType, "Error: Array out of bounds"), env) )))
        } else {
          Let(arr.toVal, transform(array, env),
            Sequence(Seq(
              ArraySet(arr, transform(index, env), maybeBox(value, AnyRefType, env)),
              arr
            )))
        }
      case s.ArraySelect(array, index) =>
        if (generateChecks) {
          val arr = Variable.fresh("array", ArrayType(AnyRefType))
          val ind = Variable.fresh("index", Int32Type())
          Let(arr.toVal, transform(array, env),
            Let(ind.toVal, transform(index, env),
              IfExpr(
                inBounds(arr, ind),
                maybeUnbox(
                  ArraySelect(arr, ind),
                  AnyRefType,
                  transform(e.getType, env),
                  env ),
                transform(s.Error(e.getType, "Error: Array out of bounds"), env) )))
        } else {
          maybeUnbox(
            ArraySelect(transform(array, env), transform(index, env)),
            AnyRefType,
            transform(e.getType, env),
            env
          )
        }

      // Tuples
      case s.Tuple(exprs) =>
        transform(s.ADT(
          lib.sort(s"Tuple${exprs.size}").constructors.head.id,
          exprs map (_.getType),
          exprs
        ), env)
      case s.TupleSelect(tuple, index) =>
        val size = tuple.getType.asInstanceOf[s.TupleType].bases.size
        val constr = lib.sort(s"Tuple$size").constructors.head
        val selector = constr.fields(index - 1).id
        maybeUnbox(
          RecordSelector(CastDown(transform(tuple, env), RecordType(constr.id)), selector),
          AnyRefType,
          transform(e.getType, env),
          env
        )

      // Sets
      case s.FiniteSet(Seq(), base) =>
        val empty = s.ADT(
          lib.sort("Set").constructors.find(_.id.name == "SNil").get.id,
          Seq(base),
          Seq()
        )
        transform(empty, env)
      case s.FiniteSet(elements, base) =>
        transform(
          elements.foldLeft[s.Expr](s.FiniteSet(Seq(), base)){ (rest, elem) =>
            s.SetAdd(rest, elem)
          },
          env )
      case s.SetAdd(set, elem) =>
        FunctionInvocation(
          lib.fun("setAdd").id, Seq(),
          Seq(transform(set, env), maybeBox(elem, AnyRefType, env))
        )
      case s.ElementOfSet(element, set) =>
        FunctionInvocation(
          lib.fun("elementOfSet").id, Seq(),
          Seq(transform(set, env), maybeBox(element, AnyRefType, env))
        )
      case s.SubsetOf(lhs, rhs) =>
        FunctionInvocation(
          lib.fun("subsetOf").id, Seq(),
          Seq(transform(lhs, env), transform(rhs, env))
        )
      case s.SetIntersection(lhs, rhs) =>
        FunctionInvocation(
          lib.fun("setIntersection").id, Seq(),
          Seq(transform(lhs, env), transform(rhs, env))
        )
      case s.SetUnion(lhs, rhs) =>
        FunctionInvocation(
          lib.fun("setUnion").id, Seq(),
          Seq(transform(lhs, env), transform(rhs, env))
        )
      case s.SetDifference(lhs, rhs) =>
        FunctionInvocation(
          lib.fun("setDifference").id, Seq(),
          Seq(transform(lhs, env), transform(rhs, env))
        )

      // Bags
      case s.FiniteBag(elements, base) =>
        val empty = s.ADT(
          lib.sort("Bag").constructors.find(_.id.name == "BNil").get.id,
          Seq(base),
          Seq()
        )
        elements.foldLeft[Expr](transform(empty, env)) {
          case (rest, (elem, mult)) =>
            FunctionInvocation(
              lib.fun("bagAdd").id, Seq(),
              Seq(rest, maybeBox(elem, AnyRefType, env), transform(mult, env))
            )
        }
      case s.BagAdd(bag, elem) =>
        FunctionInvocation(
          lib.fun("bagAdd").id, Seq(),
          Seq(
            transform(bag, env),
            maybeBox(elem, AnyRefType, env),
            transform(s.IntegerLiteral(BigInt(1)), env)
          )
        )
      case s.MultiplicityInBag(element, bag) =>
        FunctionInvocation(
          lib.fun("bagMultiplicity").id, Seq(),
          Seq(transform(bag, env), maybeBox(element, AnyRefType, env))
        )
      case s.BagIntersection(lhs, rhs) =>
        FunctionInvocation(
          lib.fun("bagIntersection").id, Seq(),
          Seq(transform(lhs, env), transform(rhs, env))
        )
      case s.BagUnion(lhs, rhs) =>
        FunctionInvocation(
          lib.fun("bagUnion").id, Seq(),
          Seq(transform(lhs, env), transform(rhs, env))
        )
      case s.BagDifference(lhs, rhs) =>
        FunctionInvocation(
          lib.fun("bagDifference").id, Seq(),
          Seq(transform(lhs, env), transform(rhs, env))
        )

      // Maps FIXME maps are wrong
      case s.FiniteMap(Seq(), default, keyType, valueType) =>
        val empty = s.ADT(
          lib.sort("Map").constructors.find(_.id.name == "MNil").get.id,
          Seq(keyType, valueType),
          Seq(default)
        )
        transform(empty, env)
      case s.FiniteMap(pairs, default, keyType, valueType) =>
        val empty = s.FiniteMap(Seq(), default, keyType, valueType)
        transform(
          pairs.foldLeft[s.Expr](empty) { case (rest, (key, value)) =>
            s.MapUpdated(rest, key, value)
          },
          env
        )
      case s.MapApply(map, key) =>
        FunctionInvocation(
          lib.fun("mapApply").id, Seq(),
          Seq(transform(map, env), maybeBox(key, AnyRefType, env))
        )
      case s.MapUpdated(map, key, value) =>
        FunctionInvocation(
          lib.fun("mapUpdated").id, Seq(),
          Seq(transform(map, env), maybeBox(key, AnyRefType, env), maybeBox(value, AnyRefType, env))
        )

      // We do not translate these for now
      case s.Forall(_, _)
         | s.Choose(_, _)
         | s.GenericValue(_, _) =>
        context.reporter.fatalError(
          s"Cannot translate expression " +
          e.asString(s.PrinterOptions.fromContext(context, Some(env.syms))) +
          " to WebAssembly."
        )

      case _ =>
        // Let, Variable, IfExpr, NoTree
        // other literals
        // string, boolean, arithmetic operations
        // ArrayLength
        super.transform(e, env)
    }
  }
}


/** Lowers stainless trees to the language defined in [[stainless.wasmgen.intermediate]]
  *
  * The following changes take place:
  * - Arrays become mutable
  * - Composite types become "records", which are extensible structs in memory. See [[Definitions.RecordSort]]
  * - Polymorphic types are erased and polymorphic values are boxed.
  * - Maps, Bags and Sets become records based on a library implemented in stainless
  *
  * Limitations:
  * - BigInts are approximated by Longs
  * - Reals are not translated (later are approximated as Doubles)
  * - ArrayUpdated does not copy, rather it does a destructive update
  */
class Lowering(context: Context) extends inox.transformers.SymbolTransformer with Lowerer {
  private val sortCodes = new inox.utils.UniqueCounter[Unit]
  locally {
    // We want to reserve the first codes for native types
    for {_ <- 0 to trees.lastReservedTag} sortCodes.nextGlobal
  }

  def transform(sort: s.ADTSort, env: Env): Seq[t.RecordSort] = {
    val eqId = FreshIdentifier(s"eq${sort.id.name}")

    val parent = new t.RecordADTSort(transform(sort.id, env)).copiedFrom(sort)

    val children = sort.constructors map { cons =>
      new t.ConstructorSort(
        transform(cons.id, env),
        parent.id,
        sortCodes.nextGlobal,
        cons.fields.map(transform(_, env))
      ).copiedFrom(cons)
    }

    parent +: children
  }

  private def mkToString(constr: s.ADTConstructor)(implicit sym: s.Symbols): s.FunDef = {
    import s._
    val dsl = new inox.ast.DSL { val trees = s }
    val sort = sym.sorts(constr.sort)
    // Make toString functions searchable in the wasm runtime library
    val funName = SymbolIdentifier(LibProvider.libPath + constr.id.uniqueName + "ToString")
    dsl.mkFunDef(funName)(sort.tparams.map(_.id.name): _*){ tps =>
      (Seq(ValDef(FreshIdentifier("v"), ADTType(sort.id, tps))), StringType(), {
        case Seq(arg) =>
          val fields = constr.typed(tps).fields
          val name = if (sort.id.name matches "Tuple\\d{1,2}") "" else constr.id.name
          if (fields.isEmpty) StringLiteral(name + "()")
          else (
            StringLiteral(name + "(") +:
            fields.zipWithIndex.flatMap { case (f, ind) =>
              val fieldStr = FunctionInvocation(
                lib.fun("toString").id,
                Seq(f.getType),
                Seq(Annotated(ADTSelector(arg, f.id), Seq(Unchecked))))
              if (ind == fields.size - 1) Seq(fieldStr)
              else Seq(fieldStr, StringLiteral(", "))
            } :+
            StringLiteral(")")
          ).reduceLeft(StringConcat)
      })
    }
  }

  def transform(syms0: s.Symbols): t.Symbols = {

    // (0) Make toString's
    val toStrings = {
      val hasBuiltinToString = Set("SCons", "SNil", "MCons", "MNil", "BCons", "BNil")
      syms0.sorts.toSeq.flatMap(_._2.constructors).filterNot( constr =>
        hasBuiltinToString contains constr.id.name
      ).map(mkToString(_)(syms0))
    }
    val syms = syms0.withFunctions(toStrings)

    // (1) Transform sorts, make them to starting symbols
    val manager = new SymbolsManager
    val env0 = Env(syms, manager, generateChecks = true)
    val initSymbols = t.NoSymbols.withRecords(syms.sorts.values.toSeq.flatMap(transform(_, env0)))

    // (2) Transform functions in program
    val tr = new ExprLowerer(manager, syms, initSymbols.records, context)
    val funs = (syms.functions mapValues tr.transform).view.force

    // (3) Put it all together
    val ret0 = t.Symbols(
      initSymbols.records ++ manager.records + (t.AnyRefSort.id -> t.AnyRefSort),
      funs ++ manager.functions
    )

    // (4) Simplify function bodies (mainly to eliminate excessive variable definitions...)
    val simplifier = ret0.simplifier(inox.solvers.PurityOptions(context))
    val ret = t.Symbols(
      ret0.records,
      ret0.functions.mapValues{ fd =>
        fd.copy(fullBody = simplifier.transform(fd.fullBody, simplifier.initEnv))
      }.view.force
    )

    //Debugging
    //implicit val printerOptions0 = s.PrinterOptions(printUniqueIds = true)
    //syms0.functions foreach (r => println(r._2.asString))
    //implicit val printerOptions = t.PrinterOptions(printUniqueIds = true)
    //ret.records foreach (r => println(r._2.asString))
    //ret.functions foreach (r => println(r._2.asString))
    //ret.functions.foreach(fn => println(ret.explainTyping(fn._2.fullBody)))

    ret
  }
}
