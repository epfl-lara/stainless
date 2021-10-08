/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

import inox.utils.Position

/** Erase value classes (ie. classes which extend [[AnyVal]])
  *
  * - Erase value classes constructors
  * - Erase field selections on value classes
  * - Erase value classes types to their underlying types
  * - Erase value classes themselves
  * - Erase implicit conversions to value classes
  */
class ValueClasses(override val s: Trees, override val t: Trees)
                  (using override val context: inox.Context)
  extends oo.CachingPhase
      with IdentitySorts
      with oo.SimpleTypeDefs { self =>

  override protected type ClassResult    = Option[t.ClassDef]
  override protected type FunctionResult = Option[t.FunDef]


  // The value class erasure transformation depends on all dependencies that ever mention a value class type

  protected val typeDefCache = new ExtractionCache[s.TypeDef, t.TypeDef]({ (td, ctx) =>
    import ctx.symbols
    TypeDefKey(td) + SetKey(
      symbols.dependencies(td.id).filter { id =>
        (symbols.dependencies(id) & ctx.valueClasses.keys.toSet).nonEmpty
      }
    )
  })

  override protected val classCache = new ExtractionCache[s.ClassDef, ClassResult]({ (cd, ctx) =>
    import ctx.symbols
    ClassKey(cd) + SetKey(
      symbols.dependencies(cd.id).filter { id =>
        (symbols.dependencies(id) & ctx.valueClasses.keys.toSet).nonEmpty
      }
    )
  })

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]({ (fd, ctx) =>
    import ctx.symbols
    FunctionKey(fd) + SetKey(
      symbols.dependencies(fd.id).filter { id =>
        (symbols.dependencies(id) & ctx.valueClasses.keys.toSet).nonEmpty
      }
    )
  })

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(self.s, self.t)(using symbols)

  protected class TransformerContext(override val s: self.s.type, override val t: self.t.type)
                                    (using val symbols: s.Symbols) extends oo.ConcreteTreeTransformer(s, t) {
    import s._
    import symbols._

    val valueClasses = symbols.classes.filter(_._2.isValueClass)

    val invariants = valueClasses.view.mapValues { cd =>
      cd.flags.collectFirst {
        case HasADTInvariant(id) => symbols.getFunction(id)
      }
    }.toMap

    val invToClass = invariants.flatMap {
      case (id, Some(inv)) => Some(inv.id -> valueClasses(id))
      case _ => None
    }.toMap

    val valueClassConversions = symbols.functions.filter { case (id, fd) =>
      fd.isSynthetic && !fd.isMethod && (fd.returnType match {
        case ClassType(id, _) => valueClasses.contains(id)
        case _ => false
      })
    }

    def baseType(ct: ClassType): Type = {
      require(valueClasses contains ct.id)
      ct.tcd.fields.head.getType
    }

    def underlyingType(ct: ClassType): Type = {
      require(valueClasses contains ct.id)
      invariants(ct.id) match {
        case Some(fd) =>
          val vd = ValDef.fresh("this", baseType(ct))
          val pred = fd.typed(ct.tps).applied(Seq(vd.toVariable))
          RefinementType(vd, pred)

        case None =>
          baseType(ct)
      }
    }

    override def transform(fd: FunDef): t.FunDef = {
      invToClass.get(fd.id) match {
        case Some(cd) =>
          val vd = fd.params.head
          val ct = vd.getType match {
            case ct: ClassType if ct.id == cd.id => ct
            case _ => context.reporter.fatalError(s"Found malformed invariant: ${fd.id.asString}")
          }

          val erased = super.transform(fd)
          val base = baseType(ct).copiedFrom(ct)
          val nvd = transform(vd.copy(tpe = base))

          erased.copy(
            params = Seq(nvd),
            fullBody = t.exprOps.preMap {
              case v: t.Variable if v.id == vd.id => Some(nvd.toVariable)
              case _ => None
            } (erased.fullBody)
          )

        case None => super.transform(fd)
      }
    }

    override def transform(tp: Type): t.Type = tp match {
      // Erase value class type to underlying type
      case ct: ClassType if valueClasses contains ct.id =>
        transform(underlyingType(ct))

      case tp => super.transform(tp)
    }

    override def transform(e: Expr): t.Expr = e match {
      // Inline invocations of implicit conversions to value class
      case fi: FunctionInvocation if valueClassConversions contains fi.id =>
        val result = exprOps.freshenLocals(fi.tfd.withParamSubst(fi.args, fi.tfd.fullBody))
        transform(result)

      // Erase constructor of value class
      case ClassConstructor(ct, Seq(arg)) if valueClasses contains ct.id =>
        val vd = t.ValDef.fresh("vc", transform(underlyingType(ct)))
        t.Let(vd.setPos(e), transform(arg).setPos(e), vd.toVariable.setPos(e)).copiedFrom(e)

      // Erase selection of underlying value on value class
      case cs @ ClassSelector(rec, _) =>
        rec.getType match {
          case ct: ClassType if valueClasses contains ct.id =>
            transform(rec)

          case _ => super.transform(cs)
        }

      case _ => super.transform(e)
    }
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): Option[t.ClassDef] = {
    if (context.valueClasses contains cd.id) None else Some(context.transform(cd))
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): Option[t.FunDef] = {
    if (context.valueClassConversions contains fd.id) None else Some(context.transform(fd))
  }

  override protected def extractTypeDef(context: TransformerContext, td: s.TypeDef): t.TypeDef = {
    context.transform(td)
  }

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def registerClasses(symbols: t.Symbols, classes: Seq[Option[t.ClassDef]]): t.Symbols =
    symbols.withClasses(classes.flatten)
}

object ValueClasses {
  def apply(ts: Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: ts.type
  } = {
    class Impl(override val s: ts.type, override val t: ts.type) extends ValueClasses(s, t)
    new Impl(ts, ts)
  }
}
