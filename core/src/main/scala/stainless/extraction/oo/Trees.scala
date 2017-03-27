/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.collection.mutable.{Map => MutableMap}

trait Trees extends holes.Trees with Definitions { self =>

  /* ========================================
   *              EXPRESSIONS
   * ======================================== */

  /** $encodingof `receiver.id[tps](args)` */
  case class MethodInvocation(receiver: Expr, id: Identifier, tps: Seq[Type], args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = receiver.getType match {
      case ct: ClassType => (s.lookupFunction(id, tps), s.lookupClass(ct.id)) match {
        case (Some(tfd), Some(cd)) => s.instantiateType(tfd.returnType, (cd.typeArgs zip ct.tps).toMap)
        case _ => Untyped
      }
      case _ => Untyped
    }
  }

  /** $encodingof `new id(args)` */
  case class ClassConstructor(ct: ClassType, args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = ct.lookupClass match {
      case Some(tcd) => checkParamTypes(args.map(_.getType), tcd.fields.map(_.tpe), ct)
      case _ => Untyped
    }
  }

  /** $encodingof `expr.selector` */
  case class ClassSelector(expr: Expr, selector: Identifier) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = expr.getType match {
      case ct: ClassType =>
        ct.getField(selector).map(_.tpe).orElse((s.lookupFunction(selector), s.lookupClass(ct.id, ct.tps)) match {
          case (Some(fd), Some(tcd)) =>
            Some(s.instantiateType(fd.returnType, (tcd.cd.tparams.map(_.tp) zip tcd.tps).toMap))
          case _ =>
            None
        }).getOrElse(Untyped)
      case _ => Untyped
    }
  }

  /** $encodingof `this` */
  case class This(ct: ClassType) extends Expr {
    def getType(implicit s: Symbols): Type = ct
  }

  /** $encodingof `super` */
  case class Super(ct: ClassType) extends Expr {
    def getType(implicit s: Symbols): Type = ct
  }


  /* ========================================
   *              EXPRESSIONS
   * ======================================== */

  /* Pattern encoding `case binder @ ct(subPatterns...) =>`
   *
   * If [[binder]] is empty, consider a wildcard `_` in its place.
   */
  case class ClassPattern(binder: Option[ValDef], tpe: ClassType, subPatterns: Seq[Pattern]) extends Pattern


  /* ========================================
   *                 TYPES
   * ======================================== */

  /** Type associated to instances of [[ClassConstructor]] */
  case class ClassType(id: Identifier, tps: Seq[Type]) extends Type {
    def lookupClass(implicit s: Symbols): Option[TypedClassDef] = s.lookupClass(id, tps)
    def tcd(implicit s: Symbols): TypedClassDef = s.getClass(id, tps)

    def getField(selector: Identifier)(implicit s: Symbols): Option[ValDef] = {
      def rec(tcd: TypedClassDef): Option[ValDef] =
        tcd.fields.collectFirst { case vd @ ValDef(`selector`, _, _) => vd }.headOption
          .orElse(tcd.parents.reverse.view.flatMap(rec).headOption)
      lookupClass.flatMap(rec)
    }
  }

  /** Top of the typing lattice, corresponds to scala's `Any` type. */
  case object AnyType extends Type

  /** Bottom of the typing lattice, corresponds to scala's `Nothing` type. */
  case object NothingType extends Type

  /** $encodingof `tp1 | ... | tpN` */
  private[oo] case class UnionType(tps: Seq[Type]) extends Type {
    override def equals(that: Any): Boolean = that match {
      case ut: UnionType => tps.toSet == ut.tps.toSet
      case _ => false
    }

    override def hashCode: Int = tps.toSet.hashCode()
  }

  /** $encodingof `tp1 & ... & tpN` */
  private[oo] case class IntersectionType(tps: Seq[Type]) extends Type {
    override def equals(that: Any): Boolean = that match {
      case it: IntersectionType => tps.toSet == it.tps.toSet
      case _ => false
    }

    override def hashCode: Int = tps.toSet.hashCode()
  }

  /** $encodingof `_ :> lo <: hi` */
  case class TypeBounds(lo: Type, hi: Type) extends Type


  /* ========================================
   *              EXTRACTORS
   * ======================================== */

  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }


  /* ========================================
   *               PRINTERS
   * ======================================== */

  protected def withSymbols[T <: Tree](elems: Seq[Either[T, Identifier]], header: String)
                                      (implicit ctx: PrinterContext): Unit = {
    new StringContext("" +: (List.fill(elems.size - 1)("\n\n") :+ "") : _*).p((for (e <- elems) yield e match {
      case Left(d) => d
      case Right(id) => {
        implicit pctx2: PrinterContext =>
          p"<unknown> $header $id"(pctx2)
      }: PrintWrapper
    }) : _*)
  }

  protected def functions(funs: Seq[Identifier]): PrintWrapper = {
    implicit pctx: PrinterContext =>
      withSymbols(funs.map(id => pctx.opts.symbols.flatMap(_.lookupFunction(id)) match {
        case Some(cd) => Left(cd)
        case None => Right(id)
      }), "def")
  }

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {

    case cd: ClassDef =>
      p"class ${cd.id}"
      p"${nary(cd.tparams, ", ", "[", "]")}"
      if (cd.fields.nonEmpty) p"(${cd.fields})"

      if (cd.parents.nonEmpty) {
        p" extends ${nary(cd.parents, " with ")}"
      }

      ctx.opts.symbols.foreach { implicit s =>
        if (cd.methods.nonEmpty) {
          p""" {
              |  ${functions(cd.methods)}
              |}"""
        }
      }

    case ClassConstructor(ct, args) =>
      p"$ct($args)"

    case ClassSelector(cls, selector) =>
      p"$cls.$selector"

    case MethodInvocation(caller, id, tps, args) =>
      p"$caller.$id${nary(tps, ", ", "[", "]")}"
      if (args.nonEmpty) {
        // TODO: handle implicit arguments and/or default values
        p"($args)"
      }

    case This(_) => p"this"

    case (tcd: TypedClassDef) => p"typed class ${tcd.id}[${tcd.tps}]"

    case _ => super.ppBody(tree)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, Some(_: ClassConstructor)) => false
    case (_, Some(MethodInvocation(_, _, _, args))) => !args.contains(ex)
    case _ => super.requiresParentheses(ex, within)
  }
}

trait TreeDeconstructor extends holes.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = e match {
    case s.MethodInvocation(rec, id, tps, args) =>
      (Seq(), rec +: args, tps, (_, es, tps) => t.MethodInvocation(es(0), id, tps, es.tail))

    case s.ClassConstructor(ct, args) =>
      (Seq(), args, Seq(ct), (_, es, tps) => t.ClassConstructor(tps.head.asInstanceOf[t.ClassType], es))

    case s.ClassSelector(expr, selector) =>
      (Seq(), Seq(expr), Seq(), (_, es, _) => t.ClassSelector(es.head, selector))

    case s.This(ct) =>
      (Seq(), Seq(), Seq(ct), (_, _, tps) => t.This(tps.head.asInstanceOf[t.ClassType]))

    case _ => super.deconstruct(e)
  }

  override def deconstruct(tpe: s.Type): (Seq[s.Type], Seq[s.Flag], (Seq[t.Type], Seq[t.Flag]) => t.Type) = tpe match {
    case s.ClassType(id, tps) => (tps, Seq(), (tps, _) => t.ClassType(id, tps))
    case s.AnyType => (Seq(), Seq(), (_, _) => t.AnyType)
    case s.NothingType => (Seq(), Seq(), (_, _) => t.NothingType)
    case s.UnionType(tps) => (tps, Seq(), (tps, _) => t.UnionType(tps))
    case s.IntersectionType(tps) => (tps, Seq(), (tps, _) => t.IntersectionType(tps))
    case s.TypeBounds(lo, hi) => (Seq(lo, hi), Seq(), (tps, _) => t.TypeBounds(tps(0), tps(1)))
    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(f: s.Flag): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Flag) = f match {
    case s.IsInvariant => (Seq(), Seq(), (_, _) => t.IsInvariant)
    case s.IsAbstract => (Seq(), Seq() ,(_, _) => t.IsAbstract)
    case s.IsSealed => (Seq(), Seq(), (_, _) => t.IsSealed)
    case s.IsMethodOf(id) => (Seq(), Seq(), (_, _) => t.IsMethodOf(id))
    case s.Bounds(lo, hi) => (Seq(), Seq(lo, hi), (_, tps) => t.Bounds(tps(0), tps(1)))
    case _ => super.deconstruct(f)
  }
}

trait TreeTransformer extends ast.TreeTransformer {
  val s: Trees
  val t: Trees

  def transform(cd: s.ClassDef): t.ClassDef = new t.ClassDef(
    cd.id,
    cd.tparams.map(tdef => transform(tdef)),
    cd.parents.map(ct => transform(ct).asInstanceOf[t.ClassType]),
    cd.fields.map(vd => transform(vd)),
    cd.flags.map(f => transform(f))
  )
}

trait SimpleSymbolTransformer extends inox.ast.SimpleSymbolTransformer {
  val s: Trees
  val t: Trees

  protected def transformClass(cd: s.ClassDef): t.ClassDef

  override def transform(syms: s.Symbols): t.Symbols = super.transform(syms)
    .withClasses(syms.classes.values.toSeq.map(transformClass))
}

object SymbolTransformer {
  def apply(trans: inox.ast.TreeTransformer { val s: Trees; val t: Trees }): inox.ast.SymbolTransformer {
    val s: trans.s.type
    val t: trans.t.type
  } = new SimpleSymbolTransformer {
    val s: trans.s.type = trans.s
    val t: trans.t.type = trans.t

    protected def transformFunction(fd: s.FunDef): t.FunDef = trans.transform(fd)
    protected def transformADT(adt: s.ADTDefinition): t.ADTDefinition = trans.transform(adt)
    protected def transformClass(cd: s.ClassDef): t.ClassDef = new t.ClassDef(
      cd.id,
      cd.tparams.map(tdef => trans.transform(tdef)),
      cd.parents.map(ct => trans.transform(ct).asInstanceOf[t.ClassType]),
      cd.fields.map(vd => trans.transform(vd)),
      cd.flags.map(f => trans.transform(f))
    )
  }
}
