/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package throwing

trait Trees extends imperative.Trees { self =>

  protected def getExceptionType(implicit s: Symbols): Option[Type] =
    s.lookup.get[ClassDef]("stainless.lang.Exception").map(cd => ClassType(cd.id, Seq()))

  /** Throwing clause of an [[ast.Expressions.Expr]]. Corresponds to the Stainless keyword *throwing*
    *
    * @param body The body of the expression. It can contain at most one [[ast.Expressions.Require]] and
    *             one [[ast.Expressions.Ensuring]] sub-expression.
    * @param pred The predicate on exceptions to satisfy. It should be a function whose argument type
    *             is `stainless.lang.Exception` and defines the exceptional cases of this function.
    */
  sealed case class Throwing(body: Expr, pred: Lambda) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = (pred.getType, getExceptionType) match {
      case (FunctionType(Seq(expType), BooleanType()), Some(tpe)) => checkParamType(tpe, expType, body.getType)
      case _ => Untyped
    }
  }

  /** Throw expression. Corresponds to the Scala keyword *throw*
    *
    * @param ex The exception to be thrown.
    */
  sealed case class Throw(ex: Expr) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = getExceptionType match {
      case Some(tpe) => checkParamType(ex.getType, tpe, NothingType())
      case _ => Untyped
    }
  }

  /** Try-catch-finally block. Corresponds to Scala's *try { ... } catch { ... } finally { ... }* */
  sealed case class Try(body: Expr, cases: Seq[MatchCase], finallizer: Option[Expr]) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = getExceptionType match {
      case Some(tpe) if (
        cases.forall { case MatchCase(pat, guard, rhs) =>
          s.patternIsTyped(tpe, pat) &&
          guard.forall(g => s.isSubtypeOf(g.getType, BooleanType()))
        } && finallizer.forall(_.isTyped)
      ) => s.leastUpperBound(body.getType +: cases.map(_.rhs.getType))

      case _ => Untyped
    }
  }

  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps

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

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Throwing(Ensuring(body, post), pred) =>
      p"""|{
          |  $body
          |} ensuring {
          |  $post
          |} throwing {
          |  $pred
          |}"""

    case Throwing(body, pred) =>
      p"""|{
          |  $body
          |} throwing {
          |  $pred
          |}"""

    case Throw(ex) =>
      p"throw $ex"

    case Try(body, cases, fin) =>
      p"""|try {
          |  $body
          |}"""
      if (cases.nonEmpty) p"""| catch {
                              |  ${nary(cases, "\n")}
                              |}"""
      if (fin.nonEmpty) p"""| finally {
                            |  ${fin.get}
                            |}"""

    case _ => super.ppBody(tree)
  }

  override protected def noBracesSub(e: Tree): Seq[Expr] = e match {
    case Throwing(bd, pred) => Seq(bd, pred)
    case Try(e, _, f) => e +: f.toSeq
    case _ => super.noBracesSub(e)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, Some(_: Throwing | _: Try)) => false
    case _ => super.requiresParentheses(ex, within)
  }
}

trait ExprOps extends imperative.ExprOps {
  protected val trees: Trees
  import trees._

  object ExceptionsKind extends SpecKind("exceptions") { type Spec = Exceptions }

  case class Exceptions(expr: Lambda) extends Specification(ExceptionsKind) {
    def map(trees: ast.Trees)(f: Expr => trees.Expr): trees.exprOps.Specification = trees match {
      case t: throwing.Trees =>
        t.exprOps.Exceptions(f(expr).asInstanceOf[t.Lambda]).asInstanceOf[trees.exprOps.Specification]
      case _ =>
        throw new java.lang.IllegalArgumentException("Can't map exceptions into non-throwing trees")
    }
  }

  override def peelSpec(expr: Expr): Option[(Specification, Expr)] = expr match {
    case Throwing(body, pred) => Some((Exceptions(pred).setPos(expr), body))
    case _ => super.peelSpec(expr)
  }

  override def applySpec(spec: Specification, body: Expr): Expr = spec match {
    case Exceptions(pred) => Throwing(body, pred).setPos(spec.getPos)
    case _ => super.applySpec(spec, body)
  }
}

trait TreeDeconstructor extends imperative.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): Deconstructed[t.Expr] = e match {
    case s.Throwing(body, pred) =>
      (Seq(), Seq(), Seq(body, pred), Seq(), Seq(), (_, _, es, _, _) => t.Throwing(es(0), es(1).asInstanceOf[t.Lambda]))

    case s.Throw(ex) =>
      (Seq(), Seq(), Seq(ex), Seq(), Seq(), (_, _, es, _, _) => t.Throw(es.head))

    case s.Try(body, cases, fin) =>
      val (cids, cvs, ces, ctps, crecons) = deconstructCases(cases)
      (cids, cvs, (body +: ces) ++ fin, ctps, Seq(), (ids, vs, es, tps, _) => {
        val newBody +: rest = es
        val (nes, newFin) = if (fin.isEmpty) (rest, None) else (rest.init, rest.lastOption)
        t.Try(newBody, crecons(ids, vs, nes, tps), newFin)
      })

    case _ => super.deconstruct(e)
  }
}
