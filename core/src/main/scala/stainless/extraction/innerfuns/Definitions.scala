/* Copyright 2009-2021 EPFL, Lausanne */

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
    def getType(using Symbols): Type = returnType.getType

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

  // We do not define Outer as a case class because the inherited `copy` method conflicts with the compiler-generated one.
  class Outer(val fd: FunDef) extends FunAbstraction(
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

    override def asString(using PrinterOptions): String = fd.asString

    // Since we want a case class behaviour, we have generated the following three methods
    def canEqual(other: Any): Boolean = other.isInstanceOf[Outer]

    override def equals(other: Any): Boolean = other match {
      case that: Outer =>
        (that canEqual this) &&
          fd == that.fd
      case _ => false
    }

    override def hashCode(): Int = {
      val state = Seq(fd)
      state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
    }
  }
  object Outer {
    def apply(fd: FunDef) = new Outer(fd)
    def unapply(i: Outer): Some[FunDef] = Some(i.fd)
  }

  // We do not define Inner as a case class because the inherited `copy` method conflics with the compiler-generated one.
  class Inner(val fd: LocalFunDef) extends FunAbstraction(
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

    override def asString(using PrinterOptions): String = fd.asString

    // Since we want a case class behaviour, we have generated the following three methods
    def canEqual(other: Any): Boolean = other.isInstanceOf[Inner]

    override def equals(other: Any): Boolean = other match {
      case that: Inner =>
        (that canEqual this) &&
          fd == that.fd
      case _ => false
    }

    override def hashCode(): Int = {
      val state = Seq(fd)
      state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
    }
  }
  object Inner {
    def apply(fd: LocalFunDef) = new Inner(fd)
    def unapply(i: Inner): Some[LocalFunDef] = Some(i.fd)
  }


  override type Symbols >: Null <: InnerFunsAbstractSymbols

  trait InnerFunsAbstractSymbols
    extends StainlessAbstractSymbols
       with innerfuns.SymbolOps
       with innerfuns.TypeOps { self0: Symbols =>
    // The only value that can be assigned to `trees`, but that has to be
    // done in a concrete class explicitly overriding `trees`
    // Otherwise, we can run into initialization issue.
    protected val trees: self.type
    // More or less the same here
    protected val symbols: this.type
  }
}

