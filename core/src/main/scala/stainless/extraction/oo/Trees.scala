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
            .map(tcd => typeOps.instantiateType(tfd.returnType, tcd.typeMap))
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
            Some(typeOps.instantiateType(fd.returnType, (tcd.cd.tparams.map(_.tp) zip tcd.tps).toMap))
          case _ =>
            None
        }).getOrElse(Untyped)
      case _ => Untyped
    }
  }

  /** $encodingof `this` */
  case class This(ct: ClassType) extends Expr with Terminal {
    def getType(implicit s: Symbols): Type = ct
  }

  /** $encodingof `super` */
  case class Super(ct: ClassType) extends Expr with Terminal {
    def getType(implicit s: Symbols): Type = ct
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

  override protected def constructorType(tcons: TypedADTConstructor): Type = {
    val v = Variable.fresh("v", ADTType(tcons.sort.id, tcons.tps))
    RefinementType(v.toVal, IsConstructor(v, tcons.id))
  }

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

  /** $encodingof `{ vd: vd.tpe | pred }` */
  case class RefinementType(vd: ValDef, pred: Expr) extends Type


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

    case AnyType() =>
      p"Any"

    case NothingType() =>
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

    case RefinementType(vd, pred) =>
      p"|{ $vd "
      ctx.sb.append("|")
      p"| $pred }"

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
    case (_, Some(MethodInvocation(_, _, _, args))) => !args.contains(ex)
    case _ => super.requiresParentheses(ex, within)
  }
}


trait TreeDeconstructor extends holes.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): DeconstructedExpr = e match {
    case s.MethodInvocation(rec, id, tps, args) =>
      (Seq(id), Seq(), rec +: args, tps, (ids, _, es, tps) => t.MethodInvocation(es(0), ids.head, tps, es.tail))

    case s.ClassConstructor(ct, args) =>
      (Seq(), Seq(), args, Seq(ct), (_, _, es, tps) => t.ClassConstructor(tps.head.asInstanceOf[t.ClassType], es))

    case s.ClassSelector(expr, selector) =>
      (Seq(selector), Seq(), Seq(expr), Seq(), (ids, _, es, _) => t.ClassSelector(es.head, ids.head))

    case s.This(ct) =>
      (Seq(), Seq(), Seq(), Seq(ct), (_, _, _, tps) => t.This(tps.head.asInstanceOf[t.ClassType]))

    case s.IsInstanceOf(e, tpe) =>
      (Seq(), Seq(), Seq(e), Seq(tpe), (_, _, es, tps) => t.IsInstanceOf(es.head, tps.head))

    case s.AsInstanceOf(e, tpe) =>
      (Seq(), Seq(), Seq(e), Seq(tpe), (_, _, es, tps) => t.AsInstanceOf(es.head, tps.head))

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

  override def deconstruct(tpe: s.Type): DeconstructedType = tpe match {
    case s.ClassType(id, tps) => (Seq(id), tps, Seq(), (ids, tps, _) => t.ClassType(ids.head, tps))
    case s.AnyType() => (Seq(), Seq(), Seq(), (_, _, _) => t.AnyType())
    case s.NothingType() => (Seq(), Seq(), Seq(), (_, _, _) => t.NothingType())
    case s.UnionType(tps) => (Seq(), tps, Seq(), (_, tps, _) => t.UnionType(tps))
    case s.IntersectionType(tps) => (Seq(), tps, Seq(), (_, tps, _) => t.IntersectionType(tps))
    case s.TypeBounds(lo, hi) => (Seq(), Seq(lo, hi), Seq(), (_, tps, _) => t.TypeBounds(tps(0), tps(1)))
    case s.RefinementType(vd, pred) =>
      def rec(e: s.Expr): (Seq[Identifier], Seq[s.Type], Seq[s.Flag], (Seq[Identifier], Seq[t.Type], Seq[t.Flag]) => t.Expr) = {
        val (ids, vs, es, tps, recons) = deconstruct(e)
        val recEs = es map rec
        (
          ids ++ recEs.flatMap(_._1),
          vs.map(_.tpe) ++ tps ++ recEs.flatMap(_._2),
          vs.flatMap(_.flags) ++ recEs.flatMap(_._3),
          (nids, ntps, nflags) => {
            val (pIds, pesIds) = nids.splitAt(ids.size)
            var rids = pesIds

            val (vsTps, restTps) = ntps.splitAt(vs.size)
            val (pTps, pesTps) = restTps.splitAt(tps.size)
            var rtps = pesTps

            val (vsFlags, restFlags) = nflags.splitAt(vs.map(_.flags.size).sum)
            var vflags = vsFlags
            var rflags = restFlags

            val nvs = for ((v, ntpe) <- vs zip vsTps) yield {
              val (nvflags, rvflags) = vflags.splitAt(v.flags.size)
              vflags = rvflags
              t.Variable(v.id, ntpe, nvflags.toSet).copiedFrom(v)
            }

            val nes = for ((eids, etps, eflags, erecons) <- recEs) yield {
              val (neids, reids) = rids.splitAt(eids.size)
              rids = reids

              val (netps, retps) = rtps.splitAt(etps.size)
              rtps = retps

              val (neflags, reflags) = rflags.splitAt(eflags.size)
              rflags = reflags

              erecons(neids, netps, neflags)
            }
            recons(pIds, nvs, nes, pTps).copiedFrom(e)
          }
        )
      }

      val (ids, tps, flags, recons) = rec(pred)
      (ids, vd.tpe +: tps, vd.flags.toSeq ++ flags, (_, tps, flags) => {
        val (vflags, pflags) = flags.splitAt(vd.flags.size)
        val npred = recons(ids, tps.tail, pflags).copiedFrom(pred)
        t.RefinementType(t.ValDef(vd.id, tps.head, vflags.toSet).copiedFrom(vd), npred).copiedFrom(tpe)
      })

    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.IsInvariant => (Seq(), Seq(), Seq(), (_, _, _) => t.IsInvariant)
    case s.IsAbstract => (Seq(), Seq(), Seq() ,(_, _, _) => t.IsAbstract)
    case s.IsSealed => (Seq(), Seq(), Seq(), (_, _, _) => t.IsSealed)
    case s.IsMethodOf(id) => (Seq(id), Seq(), Seq(), (ids, _, _) => t.IsMethodOf(ids.head))
    case s.Bounds(lo, hi) => (Seq(), Seq(), Seq(lo, hi), (_, _, tps) => t.Bounds(tps(0), tps(1)))
    case s.Variance(v) => (Seq(), Seq(), Seq(), (_, _, _) => t.Variance(v))
    case _ => super.deconstruct(f)
  }
}

trait TreeTransformer extends ast.TreeTransformer {
  val s: Trees
  val t: Trees

  override def transform(tpe: s.Type): t.Type = tpe match {
    case s.RefinementType(vd, pred) =>
      t.RefinementType(transform(vd), transform(pred)).copiedFrom(tpe)
    case _ => super.transform(tpe)
  }

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
