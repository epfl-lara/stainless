/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.collection.mutable.{Map => MutableMap}

trait Trees extends imperative.Trees with Definitions with TreeOps { self =>

  /* ========================================
   *              EXPRESSIONS
   * ======================================== */

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
            Some(typeOps.instantiateType(fd.returnType, (tcd.cd.tparams.map(_.tp) zip tcd.tps).toMap))
          case _ =>
            None
        }).getOrElse(Untyped)
      case _ => Untyped
    }
  }

  /** $encodingof `expr.isInstanceOf[tpe]` */
  case class IsInstanceOf(expr: Expr, tpe: Type) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = {
      if (s.typesCompatible(expr.getType, tpe)) BooleanType() else Untyped
    }
  }

  /** $encodingof `expr.asInstanceOf[tpe]` */
  case class AsInstanceOf(expr: Expr, tpe: Type) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = {
      if (s.typesCompatible(expr.getType, tpe)) tpe else Untyped
    }
  }


  /* ========================================
   *              PATTERNS
   * ======================================== */

  /* Pattern encoding `case binder @ ct(subPatterns...) =>`
   *
   * If [[binder]] is empty, consider a wildcard `_` in its place.
   */
  case class ClassPattern(binder: Option[ValDef], tpe: ClassType, subPatterns: Seq[Pattern]) extends Pattern

  /** Pattern encoding `case binder: ct`
   *      *
   *          * If [[binder]] is empty, consider a wildcard `_` in its place.
   *              */
  case class InstanceOfPattern(binder: Option[ValDef], tpe: Type) extends Pattern {
    val subPatterns = Seq()
  }


  /* ========================================
   *                 TYPES
   * ======================================== */

  override protected def getField(tpe: Type, selector: Identifier)(implicit s: Symbols): Option[ValDef] = tpe match {
    case ct: ClassType => ct.getField(selector)
    case _ => super.getField(tpe, selector)
  }

  /** Type associated to instances of [[ClassConstructor]] */
   case class ClassType(id: Identifier, tps: Seq[Type]) extends Type {
    def lookupClass(implicit s: Symbols): Option[TypedClassDef] = s.lookupClass(id, tps)
    def tcd(implicit s: Symbols): TypedClassDef = s.getClass(id, tps)

    def getField(selector: Identifier)(implicit s: Symbols): Option[ValDef] = {
      def rec(tcd: TypedClassDef): Option[ValDef] =
        tcd.fields.collectFirst { case vd @ ValDef(`selector`, _, _) => vd }
          .orElse(tcd.parents.reverse.view.flatMap(rec).headOption)
      lookupClass.flatMap(rec)
    }
  }

  /** Top of the typing lattice, corresponds to scala's `Any` type. */
  case class AnyType() extends Type

  /** Bottom of the typing lattice, corresponds to scala's `Nothing` type. */
  case class NothingType() extends Type

  /** $encodingof `_ :> lo <: hi` */
  case class TypeBounds(lo: Type, hi: Type) extends Type

  private def widenTypeParameter(tpe: Typed)(implicit s: Symbols): Type = tpe.getType match {
    case tp: TypeParameter => widenTypeParameter(tp.upperBound)
    case tpe => tpe
  }

  override protected def getBVType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type =
    super.getBVType(widenTypeParameter(tpe), tpes: _*)

  override protected def getADTType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type =
    super.getADTType(widenTypeParameter(tpe), tpes: _*)

  override protected def getTupleType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type =
    super.getTupleType(widenTypeParameter(tpe), tpes: _*)

  override protected def getSetType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type =
    super.getSetType(widenTypeParameter(tpe), tpes: _*)

  override protected def getBagType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type =
    super.getBagType(widenTypeParameter(tpe), tpes: _*)

  override protected def getMapType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type =
    widenTypeParameter(s.leastUpperBound(tpe +: tpes map (_.getType))) match {
      case mt: MapType => mt
      case _ => Untyped
    }


  /* ========================================
   *              EXTRACTORS
   * ======================================== */

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }
}


trait Printer extends imperative.Printer {
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

    case ClassType(id, tps) =>
      p"${id}${nary(tps, ", ", "[", "]")}"

    case AnyType() =>
      p"Any"

    case NothingType() =>
      p"Nothing"

    case TypeBounds(lo, hi) =>
      p"_ >: $lo <: $hi"

    case tpd: TypeParameterDef =>
      tpd.tp.flags collectFirst { case Variance(v) => v } foreach (if (_) p"+" else p"-")
      p"${tpd.tp}"
      tpd.tp.flags collectFirst { case Bounds(lo, hi) => (lo, hi) } foreach { case (lo, hi) =>
        if (lo != NothingType()) p" >: $lo"
        if (hi != AnyType()) p" <: $hi"
      }

    case TypeParameter(id, flags) =>
      p"$id"
      for (f <- flags if f.name != "variance" && f.name != "bounds") p" @${f.asString(ctx.opts)}"

    case ClassConstructor(ct, args) =>
      p"$ct($args)"

    case ClassSelector(cls, selector) =>
      p"$cls.$selector"

    case IsInstanceOf(e, tpe) =>
      p"$e.isInstanceOf[$tpe]"

    case AsInstanceOf(e, tpe) =>
      p"$e.asInstanceOf[$tpe]"

    case ClassPattern(ob, ct, subs) =>
      ob foreach (vd => p"${vd.toVariable} @ ")
      printNameWithPath(ct.id) // no type parameters in patterns
      p"($subs)"

    case InstanceOfPattern(ovd, tpe) =>
      ovd foreach (vd => p"${vd.toVariable} : ")
      p"$tpe"

    case (tcd: TypedClassDef) => p"typed class ${tcd.id}[${tcd.tps}]"

    case _ => super.ppBody(tree)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, Some(_: ClassConstructor)) => false
    case _ => super.requiresParentheses(ex, within)
  }
}


trait TreeDeconstructor extends imperative.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): Deconstructed[t.Expr] = e match {
    case s.ClassConstructor(ct, args) =>
      (Seq(), Seq(), args, Seq(ct), Seq(), (_, _, es, tps, _) => t.ClassConstructor(tps.head.asInstanceOf[t.ClassType], es))

    case s.ClassSelector(expr, selector) =>
      (Seq(selector), Seq(), Seq(expr), Seq(), Seq(), (ids, _, es, _, _) => t.ClassSelector(es.head, ids.head))

    case s.IsInstanceOf(e, tpe) =>
      (Seq(), Seq(), Seq(e), Seq(tpe), Seq(), (_, _, es, tps, _) => t.IsInstanceOf(es.head, tps.head))

    case s.AsInstanceOf(e, tpe) =>
      (Seq(), Seq(), Seq(e), Seq(tpe), Seq(), (_, _, es, tps, _) => t.AsInstanceOf(es.head, tps.head))

    case _ => super.deconstruct(e)
  }

  override def deconstruct(pattern: s.Pattern): DeconstructedPattern = pattern match {
    case s.ClassPattern(binder, ct, subs) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(), Seq(ct), subs, (_, vs, _, tps, subs) => {
        t.ClassPattern(vs.headOption.map(_.toVal), tps.head.asInstanceOf[t.ClassType], subs)
      })
    case s.InstanceOfPattern(binder, ct) =>
      (Seq(), binder.map(_.toVariable).toSeq, Seq(), Seq(ct), Seq(), (_, vs, _, tps, _) => {
        t.InstanceOfPattern(vs.headOption.map(_.toVal), tps.head)
      })
    case _ => super.deconstruct(pattern)
  }

  override def deconstruct(tpe: s.Type): Deconstructed[t.Type] = tpe match {
    case s.ClassType(id, tps) => (Seq(id), Seq(), Seq(), tps, Seq(), (ids, _, _, tps, _) => t.ClassType(ids.head, tps))
    case s.AnyType() => (Seq(), Seq(), Seq(), Seq(), Seq(), (_, _, _, _, _) => t.AnyType())
    case s.NothingType() => (Seq(), Seq(), Seq(), Seq(), Seq(), (_, _, _, _, _) => t.NothingType())
    case s.TypeBounds(lo, hi) => (Seq(), Seq(), Seq(), Seq(lo, hi), Seq(), (_, _, _, tps, _) => t.TypeBounds(tps(0), tps(1)))
    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.IsCaseObject => (Seq(), Seq(), Seq(), (_, _, _) => t.IsCaseObject)
    case s.IsInvariant => (Seq(), Seq(), Seq(), (_, _, _) => t.IsInvariant)
    case s.IsAbstract => (Seq(), Seq(), Seq() ,(_, _, _) => t.IsAbstract)
    case s.IsSealed => (Seq(), Seq(), Seq(), (_, _, _) => t.IsSealed)
    case s.Bounds(lo, hi) => (Seq(), Seq(), Seq(lo, hi), (_, _, tps) => t.Bounds(tps(0), tps(1)))
    case s.Variance(v) => (Seq(), Seq(), Seq(), (_, _, _) => t.Variance(v))
    case _ => super.deconstruct(f)
  }
}

trait TreeOps extends ast.TreeOps { self: Trees =>

  trait TreeTraverser extends super.TreeTraverser {
    def traverse(cd: ClassDef): Unit = {
      cd.tparams.foreach(traverse)
      cd.parents.foreach(traverse)
      cd.fields.foreach(traverse)
      cd.flags.foreach(traverse)
    }
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
    protected def transformSort(sort: s.ADTSort): t.ADTSort = trans.transform(sort)
    protected def transformClass(cd: s.ClassDef): t.ClassDef = new t.ClassDef(
      cd.id,
      cd.tparams.map(tdef => trans.transform(tdef)),
      cd.parents.map(ct => trans.transform(ct).asInstanceOf[t.ClassType]),
      cd.fields.map(vd => trans.transform(vd)),
      cd.flags.map(f => trans.transform(f))
    ).copiedFrom(cd)
  }
}
