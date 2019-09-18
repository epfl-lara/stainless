/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

trait Definitions extends extraction.Trees { self: Trees =>

  case class LocalFunDef(
    id: Identifier,
    tparams: Seq[TypeParameterDef],
    params: Seq[ValDef],
    returnType: Type,
    fullBody: Expr,
    flags: Seq[Flag]
  ) extends Definition {
    def getType(implicit s: Symbols): Type = returnType.getType

    def freeVariables: Set[Variable] =
      tparams.flatMap(tpd => typeOps.variablesOf(tpd.tp)).toSet ++
      params.foldRight(typeOps.variablesOf(returnType) ++ exprOps.variablesOf(fullBody)) {
        case (vd, vars) => vars - vd.toVariable ++ typeOps.variablesOf(vd.tpe)
      }
  }


  /** Abstraction over [[FunDef]] and [[LocalFunDef]] to provide a unified interface to both
    * of them as these are generally not distinguished during program transformations. */
  sealed abstract class FunAbstraction(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val params: Seq[ValDef],
    val returnType: Type,
    val fullBody: Expr,
    val flags: Seq[Flag]
  ) extends Tree {
    def copy(
      id: Identifier = id,
      tparams: Seq[TypeParameterDef] = tparams,
      params: Seq[ValDef] = params,
      returnType: Type = returnType,
      fullBody: Expr = fullBody,
      flags: Seq[Flag] = flags
    ): FunAbstraction = to(self)(id, tparams, params, returnType, fullBody, flags)

    def to(t: Trees)(
      id: Identifier,
      tparams: Seq[t.TypeParameterDef],
      params: Seq[t.ValDef],
      returnType: t.Type,
      fullBody: t.Expr,
      flags: Seq[t.Flag]
    ): t.FunAbstraction

    def toFun: FunDef = asInstanceOf[Outer].fd
    def toLocal: LocalFunDef = asInstanceOf[Inner].fd
  }

  case class Outer(fd: FunDef) extends FunAbstraction(
    fd.id, fd.tparams, fd.params, fd.returnType, fd.fullBody, fd.flags) {
    setPos(fd)

    def to(t: Trees)(
      id: Identifier,
      tparams: Seq[t.TypeParameterDef],
      params: Seq[t.ValDef],
      returnType: t.Type,
      fullBody: t.Expr,
      flags: Seq[t.Flag]
    ): t.Outer = t.Outer(new t.FunDef(id, tparams, params, returnType, fullBody, flags).copiedFrom(fd))

    override def asString(implicit popts: PrinterOptions): String = fd.asString
  }

  case class Inner(fd: LocalFunDef) extends FunAbstraction(
    fd.id, fd.tparams, fd.params, fd.returnType, fd.fullBody, fd.flags) {
    setPos(fd)

    def to(t: Trees)(
      id: Identifier,
      tparams: Seq[t.TypeParameterDef],
      params: Seq[t.ValDef],
      returnType: t.Type,
      fullBody: t.Expr,
      flags: Seq[t.Flag]
    ): t.Inner = t.Inner(t.LocalFunDef(id, tparams, params, returnType, fullBody, flags).copiedFrom(fd))

    override def asString(implicit popts: PrinterOptions): String = fd.asString
  }


  override type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols
      with SymbolOps
      with TypeOps { self0: Symbols =>

  }
}

