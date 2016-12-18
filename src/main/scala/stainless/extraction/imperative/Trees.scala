/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait Trees extends innerfuns.Trees { self =>

  /* XLang imperative trees to desugar */

  /** $encodingof `{ expr1; expr2; ...; exprn; last }` */
  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = if (exprs.forall(_.isTyped)) last.getType else Untyped
  }

  /** $encoding of `var vd = value; body` */
  case class LetVar(vd: ValDef, value: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (s.isSubtypeOf(value.getType, vd.tpe)) body.getType
      else Untyped
    }
  }

  /** $encodingof `vd = value` */
  case class Assignment(v: Variable, value: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = if (s.isSubtypeOf(value.getType, v.tpe)) {
      UnitType
    } else {
      Untyped
    }
  }

  /** $encodingof `obj.selector = value` */
  case class FieldAssignment(obj: Expr, selector: Identifier, value: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      def fromConstr(tp: TypedADTConstructor): Option[Type] = {
        tp.fields
          .find(_.id == selector)
          .filter(vd => s.isSubtypeOf(value.getType, vd.tpe))
          .map(_ => UnitType)
      }

      obj.getType match {
        case ct: ADTType => (ct.lookupADT.get match {
          case at: TypedADTSort =>
            at.constructors.flatMap(fromConstr)
          case ac: TypedADTConstructor =>
            fromConstr(ac).toSeq
        }).headOption.getOrElse(Untyped)

        case _ => Untyped
      }
    }
  }

  /** $encodingof `(while(cond) { ... }) invariant (pred)` */
  case class While(cond: Expr, body: Expr, pred: Option[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      if (cond.getType == BooleanType && body.isTyped && pred.forall(_.getType == BooleanType)) UnitType
      else Untyped
  }

  /** $encodingof `array(index) = value` */
  case class ArrayUpdate(array: Expr, index: Expr, value: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = (array.getType, index.getType) match {
      case (ArrayType(base), Int32Type) if s.isSubtypeOf(value.getType, base) => UnitType
      case _ => Untyped
    }
  }

  /** $encodingof `old(e)` */
  case class Old(e: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = e.getType
  }


  /** Abstraction over [[FunDef]] and [[LocalFunDef]] to provide a unified interface to both
    * of them as these are generally not distinguished during imperative code elimination. */
  sealed abstract class FunAbstraction(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val params: Seq[ValDef],
    val returnType: Type,
    val body: Expr,
    val flags: Set[Flag]
  ) extends inox.utils.Positioned {
    def copy(
      id: Identifier = id,
      tparams: Seq[TypeParameterDef] = tparams,
      params: Seq[ValDef] = params,
      returnType: Type = returnType,
      body: Expr = body,
      flags: Set[Flag] = flags
    ): FunAbstraction

    def toFun: FunDef = asInstanceOf[Outer].fd
    def toLocal: LocalFunDef = asInstanceOf[Inner].fd
  }

  case class Outer(fd: FunDef)(implicit s: Symbols) extends FunAbstraction(
    fd.id, fd.tparams, fd.params, fd.returnType, fd.fullBody, fd.flags) {
    setPos(fd)

    def copy(
      id: Identifier = id,
      tparams: Seq[TypeParameterDef] = tparams,
      params: Seq[ValDef] = params,
      returnType: Type = returnType,
      body: Expr = body,
      flags: Set[Flag] = flags
    ): Outer = Outer(fd.copy(
      id = id,
      tparams = tparams,
      params = params,
      returnType = returnType,
      fullBody = body,
      flags = flags
    ))
  }

  case class Inner(fd: LocalFunDef)(implicit s: Symbols) extends FunAbstraction(
    fd.name.id, fd.tparams, fd.body.args, fd.name.getType.asInstanceOf[FunctionType].to, fd.body.body, Set.empty) {
    setPos(fd.name)

    def copy(
      id: Identifier = id,
      tparams: Seq[TypeParameterDef] = tparams,
      params: Seq[ValDef] = params,
      returnType: Type = returnType,
      body: Expr = body,
      flags: Set[Flag] = flags
    ): Inner = Inner(fd.copy(
      name = fd.name.copy(id = id, tpe = FunctionType(params.map(_.tpe), returnType).copiedFrom(returnType)),
      tparams = tparams,
      body = Lambda(params, body).copiedFrom(body)
    ))
  }


  object VarDef {
    def apply(id: Identifier, tpe: Type, flags: Set[Flag]): ValDef = ValDef(id, tpe, flags + IsVar)
    def unapply(d: Definition): Option[(Identifier, Type, Set[Flag])] = d match {
      case vd: ValDef if vd.flags(IsVar) => Some((vd.id, vd.tpe, vd.flags))
      case _ => None
    }
  }

  override implicit def convertToVal = new VariableConverter[ValDef] {
    def convert(vs: VariableSymbol): ValDef = vs match {
      case VarDef(id, tpe, flags) => ValDef(id, tpe, flags - IsVar)
      case vd: ValDef => vd
      case _ => ValDef(vs.id, vs.tpe, Set.empty)
    }
  }

  implicit class VariableSymbolToVar(vs: VariableSymbol) {
    def toVar: ValDef = vs match {
      case vd: ValDef if vd.flags contains IsVar => vd
      case vd: ValDef => VarDef(vd.id, vd.tpe, vd.flags + IsVar)
      case _ => ValDef(vs.id, vs.tpe, Set(IsVar))
    }
  }

  case object IsVar extends Flag("var", Seq.empty)
  case object IsPure extends Flag("pure", Seq.empty)
  case object IsMutable extends Flag("mutable", Seq.empty)

  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps


  /* ========================================
   *               EXTRACTORS
   * ======================================== */

  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees =>new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }


  /* ========================================
   *               PRINTERS
   * ======================================== */

  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Block(exprs, last) =>
      p"${nary(exprs :+ last, "\n")}"

    case LetVar(vd, value, expr) =>
      p"""|var $vd = $value
          |$expr"""

    case Assignment(v, value) =>
      p"$v = $value"

    case FieldAssignment(obj, selector, value) =>
      p"$obj.$selector = $value"

    case While(cond, body, inv) =>
      inv.foreach(p => p"""|@invariant($p)
                           |""")
      p"""|while ($cond) {
          |  $body
          |}"""

    case ArrayUpdate(array, index, value) =>
      p"$array($index) = $value"

    case Old(e) =>
      p"old($e)"

    case _ => super.ppBody(tree)
  }

  override protected def isSimpleExpr(e: Expr): Boolean = e match {
    case (_: Block) | (_: LetVar) => false
    case _ => super.isSimpleExpr(e)
  }

  override protected def noBracesSub(e: Tree): Seq[Expr] = e match {
    case LetVar(_, _, bd) => Seq(bd)
    case _ => super.noBracesSub(e)
  }

  override protected def requiresBraces(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_: Expr, Some(_: Block)) => false
    case (_: Block, Some(_: While)) => false
    case _ => super.requiresBraces(ex, within)
  }
}


trait TreeDeconstructor extends innerfuns.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = e match {
    case s.Block(exprs, last) =>
      (Seq(), exprs :+ last, Seq(), (_, es, _) => t.Block(es.init, es.last))

    case s.LetVar(vd, value, expr) =>
      (Seq(vd.toVariable), Seq(value, expr), Seq(), (vs, es, _) => t.LetVar(vs.head.toVal, es(0), es(1)))

    // @nv: we DON'T return `v` as a variable here as it should not be removed from the
    //      set of free variables in `e`!
    case s.Assignment(v, value) =>
      (Seq(), Seq(v, value), Seq(), (_, es, _) => t.Assignment(es(0).asInstanceOf[t.Variable], es(1)))

    case s.FieldAssignment(obj, selector, value) =>
      (Seq(), Seq(obj, value), Seq(), (_, es, _) => t.FieldAssignment(es(0), selector, es(1)))

    case s.While(cond, body, pred) =>
      (Seq(), Seq(cond, body) ++ pred, Seq(), (_, es, _) => t.While(es(0), es(1), es.drop(2).headOption))

    case s.ArrayUpdate(array, index, value) =>
      (Seq(), Seq(array, index, value), Seq(), (_, es, _) => t.ArrayUpdate(es(0), es(1), es(2)))

    case s.Old(e) =>
      (Seq(), Seq(e), Seq(), (_, es, _) => t.Old(es.head))

    case _ => super.deconstruct(e)
  }

  override def deconstruct(f: s.Flag): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Flag) = f match {
    case s.IsVar => (Seq(), Seq(), (_, _) => t.IsVar)
    case s.IsPure => (Seq(), Seq(), (_, _) => t.IsPure)
    case s.IsMutable => (Seq(), Seq(), (_, _) => t.IsMutable)
    case _ => super.deconstruct(f)
  }
}

trait ExprOps extends innerfuns.ExprOps {
  protected val trees: Trees
  import trees._

  def flattenBlocks(expr: Expr): Expr = postMap {
    case Block(exprs, last) =>
      val newExprs = (exprs.filter(_ != UnitLiteral()) :+ last).flatMap {
        case Block(es, l) => es :+ l
        case e => Seq(e)
      }

      Some(newExprs match {
        case Seq() => UnitLiteral()
        case Seq(e) => e
        case es => Block(es.init, es.last)
      })
    case _ => None
  } (expr)

  /** Traverses [[expr]] top-down and _as soon as_ a visited expression occurs
    * in the [[subst]] map, replaces it by the corresponding image. The function
    * is NOT called recursively on the image!
    *
    * We use this to replace `Old(v)` expressions at the same time as we're
    * rewritting the `v` variable to some other expression. The non-recursivity
    * enables us to exclusively update one or the other.
    */
  def replaceSingle(subst: Map[Expr, Expr], expr: Expr): Expr = {
    def rec(e: Expr): Expr = subst.get(e) match {
      case Some(img) => img
      case None =>
        val Operator(es, recons) = e
        val newEs = es.map(rec)
        if ((es zip newEs) exists (p => p._1 ne p._2)) {
          recons(newEs)
        } else {
          e
        }
    }

    rec(expr)
  }
}
