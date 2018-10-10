/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package utils

import scala.collection._

trait Canonization { self =>

  val trees: stainless.ast.Trees
  lazy val s: self.trees.type = self.trees
  lazy val t: self.trees.type = self.trees

  import self.trees._

  type VC = verification.VC[trees.type]

  protected class IdTransformer(val symbols: trees.Symbols) extends transformers.TreeTransformer {
    val s: self.trees.type = self.trees
    val t: self.trees.type = self.trees

    // Stores the transformed function and ADT definitions
    private var transformedFunctions = new scala.collection.mutable.ListBuffer[FunDef]()
    private var transformedSorts = new scala.collection.mutable.ListBuffer[ADTSort]()

    private var localCounter = 0
    // Maps an original identifier to a normalized identifier
    protected final val ids: mutable.Map[Identifier, Identifier] = mutable.Map.empty

    protected final def freshId(): Identifier = {
      localCounter = localCounter + 1
      new Identifier("x",localCounter,localCounter)
    }

    override def transform(id: Identifier): Identifier = {
      val visited = ids contains id
      val nid = ids.getOrElseUpdate(id, freshId())

      if ((symbols.functions contains id) && !visited) {
        transformedFunctions += transform(symbols.functions(id))
      } else if ((symbols.sorts contains id) && !visited) {
        transformedSorts += transform(symbols.sorts(id))
      }

      nid
    }

    final def functions: Seq[FunDef] = transformedFunctions.toSeq
    final def sorts: Seq[ADTSort] = transformedSorts.toSeq
  }

  def apply(syms: Symbols, expr: Expr): (Symbols, Expr) = {
    val transformer = new IdTransformer(syms)
    val newExpr = transformer.transform(expr)
    val newSyms = NoSymbols.withFunctions(transformer.functions).withSorts(transformer.sorts)
    (newSyms, newExpr)
  }

  def apply(syms: Symbols): Symbols = {
    import exprOps._
    import syms._

    implicit object functionOrdering extends Ordering[FunDef] {
      private val sizeAndName: Ordering[FunDef] = Ordering.by(fd => (formulaSize(fd.fullBody), fd.id.name))

      override def compare(fd1: FunDef, fd2: FunDef): Int = {
        if (transitivelyCalls(fd1, fd2) && !transitivelyCalls(fd2, fd1)) 1
        else if (transitivelyCalls(fd2, fd1) && !transitivelyCalls(fd1, fd2)) -1
        else sizeAndName.compare(fd1, fd2)
      }
    }

    val transformer = new IdTransformer(syms)
    val newFunctions = syms.functions.values.toSeq.sorted.map(transformer.transform)

    // There may be some sorts in `syms.sorts` that have not yet been seen by `transformer`.
    // We therefore sort `syms.sorts` by their name to make the traversal deterministic.
    // This means that sort normalization depends on the sort names, but such cases should be quite
    // rare and we assume the names would then remain stable.
    val newSorts = syms.sorts.values.toSeq.sortBy(_.id.name).map(transformer.transform)

    NoSymbols.withFunctions(newFunctions).withSorts(newSorts)
  }

  protected class RegisteringTransformer extends transformers.TreeTransformer {
    val s: self.trees.type = self.trees
    val t: self.trees.type = self.trees

    private var localCounter = 0
    // Maps an original identifier to a normalized identifier
    protected final val ids: mutable.Map[Identifier, Identifier] = mutable.Map.empty

    final def registerId(id: Identifier): Identifier = ids.getOrElseUpdate(id, {
      localCounter = localCounter + 1
      new Identifier("x",localCounter,localCounter)
    })

    override def transform(id: Identifier): Identifier = ids.getOrElse(id, id)

    override def transform(vd: ValDef): ValDef = {
      registerId(vd.id)
      super.transform(vd)
    }

    override def transform(tp: TypeParameterDef): TypeParameterDef = {
      registerId(tp.id)
      super.transform(tp)
    }

    override def transform(e: Expr): Expr = e match {
      case v: Variable =>
        registerId(v.id)
        super.transform(v)
      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case tp: TypeParameter =>
        registerId(tp.id)
        super.transform(tp)
      case _ => super.transform(tpe)
    }
  }

  def apply(expr: Expr): Expr = {
    val transformer = new RegisteringTransformer
    transformer.transform(expr)
  }

  def apply(fd: FunDef): FunDef = {
    val transformer = new RegisteringTransformer
    transformer.registerId(fd.id)
    transformer.transform(fd)
  }

  def apply(sort: ADTSort): ADTSort = {
    val transformer = new RegisteringTransformer
    transformer.registerId(sort.id)
    transformer.transform(sort)
  }
}

trait XlangCanonization extends Canonization {
  val trees: extraction.xlang.Trees
  import trees._

  protected class RegisteringTransformer
    extends super.RegisteringTransformer
       with extraction.oo.TreeTransformer

  def apply(cd: ClassDef): ClassDef = {
    val transformer = new RegisteringTransformer
    transformer.registerId(cd.id)
    transformer.transform(cd)
  }
}


object Canonization {
  def apply(p: inox.Program { val trees: ast.Trees }): Canonization { val trees: p.trees.type } = new {
    override val trees: p.trees.type = p.trees
  } with Canonization

  def apply(tr: ast.Trees): Canonization { val trees: tr.type } = new {
    override val trees: tr.type = tr
  } with Canonization
}

object XlangCanonization {
  def apply(p: inox.Program { val trees: extraction.xlang.Trees }): XlangCanonization { val trees: p.trees.type } = new {
    override val trees: p.trees.type = p.trees
  } with XlangCanonization

  def apply(tr: extraction.xlang.Trees): XlangCanonization { val trees: tr.type } = new {
    override val trees: tr.type = tr
  } with XlangCanonization

}
