/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package inlining

trait Trees extends extraction.Trees { self =>

  case object Inline extends Flag("inline", Seq())

  override def extractFlag(name: String, args: Seq[Any]): Flag = (name, args) match {
    case ("inline", Seq()) => Inline
    case _ => super.extractFlag(name, args)
  }

  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }
}

trait TreeDeconstructor extends extraction.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(f: s.Flag): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Flag) = f match {
    case s.Inline => (Seq(), Seq(), (_, _) => t.Inline)
    case _ => super.deconstruct(f)
  }
}
