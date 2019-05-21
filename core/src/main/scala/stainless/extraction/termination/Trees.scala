/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package termination

trait Trees extends extraction.Trees { self =>

  override def extractFlag(name: String, args: Seq[Expr]): Flag = (name, args) match {
    case _ => super.extractFlag(name, args)
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }
}

trait Printer extends extraction.Printer {
  protected val trees: Trees
}

trait TreeDeconstructor extends extraction.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case _ => super.deconstruct(f)
  }
}
