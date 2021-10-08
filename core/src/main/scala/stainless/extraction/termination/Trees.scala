/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package termination

trait Trees extends extraction.Trees { self =>

  case object Induct extends Flag("induct", Seq())

  override def extractFlag(name: String, args: Seq[Expr]): Flag = (name, args) match {
    case ("induct", Seq()) => Induct
    case _ => super.extractFlag(name, args)
  }

  override def getDeconstructor(
      that: inox.ast.Trees
  ): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: (Trees & that.type) => // The `& that.type` trick allows to convince scala that `tree` and `that` are actually equal...
      class DeconstructorImpl(override val s: self.type, override val t: tree.type & that.type) extends ConcreteTreeDeconstructor(s, t)
      new DeconstructorImpl(self, tree)

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
    case s.Induct => (Seq(), Seq(), Seq(), (_, _, _) => t.Induct)
    case _ => super.deconstruct(f)
  }
}

class ConcreteTreeDeconstructor(override val s: Trees, override val t: Trees) extends TreeDeconstructor