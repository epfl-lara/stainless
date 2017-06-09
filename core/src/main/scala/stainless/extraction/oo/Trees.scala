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
      case ct: ClassType => (s.lookupFunction(id, tps), ct.lookupClass) match {
        case (Some(tfd), Some(tcd)) =>
          tfd.fd.flags.collectFirst { case IsMethodOf(cid) => cid }
            .flatMap(cid => (tcd +: tcd.ancestors).find(_.id == cid))
            .map(tcd => s.instantiateType(tfd.returnType, tcd.typeMap))
            .getOrElse(Untyped)
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

  /** Type associated to instances of [[ClassConstructor]]
    * 
    * Note: this class MUST extend `ADTType` in order for `FieldAssignment` to typecheck! */
  class ClassType(id: Identifier, tps: Seq[Type]) extends ADTType(id, tps) {
    def lookupClass(implicit s: Symbols): Option[TypedClassDef] = s.lookupClass(id, tps)
    def tcd(implicit s: Symbols): TypedClassDef = s.getClass(id, tps)

    override def getField(selector: Identifier)(implicit s: Symbols): Option[ValDef] = {
      def rec(tcd: TypedClassDef): Option[ValDef] =
        tcd.fields.collectFirst { case vd @ ValDef(`selector`, _, _) => vd }
          .orElse(tcd.parents.reverse.view.flatMap(rec).headOption)
      lookupClass.flatMap(rec)
    }

    override def copy(id: Identifier = id, tps: Seq[Type] = tps) = new ClassType(id, tps)
    override def equals(that: Any): Boolean = that match {
      case ct: ClassType => id == ct.id && tps == ct.tps
      case _ => false
    }
  }

  object ClassType {
    def apply(id: Identifier, tps: Seq[Type]): ClassType = new ClassType(id, tps)
    def unapply(tpe: Type): Option[(Identifier, Seq[Type])] = tpe match {
      case ct: ClassType => Some((ct.id, ct.tps))
      case _ => None
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
}


trait Printer extends holes.Printer {
  protected val trees: Trees
  import trees._

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

    case ClassType(id, tps) =>
      p"${id}${nary(tps, ", ", "[", "]")}"

    case AnyType =>
      p"Any"

    case NothingType =>
      p"Nothing"

    case UnionType(tps) =>
      var first = true
      for (tp <- tps) {
        if (!first) p"${" | "}" // weird construction because of stripMargin
        first = false
        p"$tp"
      }

    case IntersectionType(tps) =>
      p"${nary(tps, " & ")}"

    case TypeBounds(lo, hi) =>
      p"_ >: $lo <: $hi"

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

    case ClassPattern(ob, ct, subs) =>
      ob foreach (vd => p"${vd.toVariable} @ ")
      printNameWithPath(ct.id) // no type parameters in patterns
      p"($subs)"

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

  override def deconstruct(pattern: s.Pattern): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], Seq[s.Pattern], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type], Seq[t.Pattern]) => t.Pattern) = pattern match {
    case s.ClassPattern(binder, ct, subs) =>
      (binder.map(_.toVariable).toSeq, Seq(), Seq(ct), subs, (vs, _, tps, subs) => {
        t.ClassPattern(vs.headOption.map(_.toVal), tps.head.asInstanceOf[t.ClassType], subs)
      })

    case _ => super.deconstruct(pattern)
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
  ).copiedFrom(cd)
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
    ).copiedFrom(cd)
  }
}
