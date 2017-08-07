/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package holes

import scala.collection.immutable.HashMap

trait Trees extends imperative.Trees { self =>
  case class Hole(tp: Type) extends Expr {
    override def getType(implicit s: Symbols): Type = tp
  }

  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[inox.ast.TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }
}

trait Printer extends imperative.Printer {
  protected val trees: Trees
  import trees._

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Hole(tp) => p"???[$tp]"
    case _ => super.ppBody(tree)
  }
}

trait TreeDeconstructor extends imperative.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def buildExprTableDispatch: ExpressionTableDispatch = super.buildExprTableDispatch ++ HashMap[Class[_], s.Expr => DeconstructedExpr](
    classOf[s.Hole] -> { expr =>
      val s.Hole(tp) = expr
      (Seq(), Seq(), Seq(tp), (_, _, tps) => t.Hole(tps.head))
    }
  )
}
