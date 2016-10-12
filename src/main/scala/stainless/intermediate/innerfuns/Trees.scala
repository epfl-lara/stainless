/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package intermediate
package innerfuns

import inox.ast.Identifier

trait Trees extends stainless.ast.Trees { self =>

  case class LocalFunDef(name: ValDef, tparams: Seq[TypeParameterDef], body: Lambda)

  case class LetRec(fds: Seq[LocalFunDef], body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      body.getType //FIXME
    }
  }

  case class ApplyLetRec(fun: Variable, tparams: Seq[TypeParameterDef], args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      import s._
      fun.getType match {
        case FunctionType(from, to) =>
          canBeSubtypeOf(tupleTypeWrap(args.map(_.getType)), tupleTypeWrap(from)) match {
            case Some(map) if map.keySet subsetOf tparams.toSet.map((td: TypeParameterDef ) => td.tp) =>
              instantiateType(to, map)
            case _ => Untyped
          }
        case _ =>
          Untyped
      }
    }
  }

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case LetRec(defs, body) =>
      defs foreach { case (LocalFunDef(name, tparams, Lambda(args, body))) =>
        p"""|def $name[$tparams]($args) = {
            |  $body"
            |}
            |"""
      }
      p"$body"

    case ApplyLetRec(fun, tparams, args) =>
      p"$fun[$tparams]($args)"

    case _ => super.ppBody(tree)
  }

  override def requiresBraces(ex: Tree, within: Option[Tree]) = (ex, within) match {
    case (_, Some(_:LetRec)) => false
    case _ => super.requiresBraces(ex, within)
  }

  override val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
  } = new TreeDeconstructor {
    protected val s: self.type = self
    protected val t: self.type = self
  }

  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps
}

trait TreeDeconstructor extends ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = e match {
    case s.LetRec(defs, body) =>
      (
        defs map (_.name.toVariable),
        defs.map(_.body) :+ body,
        defs.flatMap(_.tparams).map(_.tp),
        (vs, es, tps) => {
          var restTps = tps
          var restFuns = defs
          t.LetRec(
            vs.zip(es.init).map{ case (v, e) =>
              val howMany = defs.head.tparams.size
              val (tps, rest) = restTps splitAt howMany
              restTps = restTps drop howMany
              restFuns = restFuns.tail
              t.LocalFunDef(v.toVal, tps.map(tp => t.TypeParameterDef(tp.asInstanceOf[t.TypeParameter])), e.asInstanceOf[t.Lambda])
            },
            es.last
          )
        }
      )
    case s.ApplyLetRec(fun, tparams, args) =>
      (
        Seq(fun),
        args,
        tparams map (_.tp),
        (vs, es, tparams) => t.ApplyLetRec(vs.head, tparams.map(tp => t.TypeParameterDef(tp.asInstanceOf[t.TypeParameter])), es)
      )
    case other =>
      super.deconstruct(other)
  }

}

trait ExprOps extends ast.ExprOps {
  protected val trees: Trees
  import trees._
  /** Returns functions in directly nested LetDefs */
  def directlyNestedFunDefs(e: Expr): Set[LocalFunDef] = {
    fold[Set[LocalFunDef]]{
      case (LetRec(fds,_), fromFdsFromBd) => fromFdsFromBd.last ++ fds
      case (_,             subs)          => subs.flatten.toSet
    }(e)
  }

  def innerFunctionCalls(e: Expr) = {
    collect[Identifier] {
      case ApplyLetRec(fd, _, _) => Set(fd.id)
      case _ => Set()
    }(e)
  }
}