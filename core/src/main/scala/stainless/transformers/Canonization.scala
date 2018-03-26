/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package transformers

import stainless.extraction.inlining.Trees

import scala.collection._

trait Canonization { self =>

  val trees: stainless.ast.Trees
  lazy val s: self.trees.type = self.trees
  lazy val t: self.trees.type = self.trees

  import self.trees._

  type VC = verification.VC[trees.type]

  def normalize(syms: s.Symbols, vc: VC): (t.Symbols, Expr) = {

    // Stores the transformed function and ADT definitions
    var functions = Seq[FunDef]()
    var sorts = Seq[ADTSort]()

    object IdTransformer extends inox.ast.TreeTransformer {
      val s: self.trees.type = self.trees
      val t: self.trees.type = self.trees

      var localCounter = 0
      // Maps an original identifier to a normalized identifier
      val ids: mutable.Map[Identifier, Identifier] = mutable.Map.empty

      def freshId(): Identifier = {
        localCounter = localCounter + 1
        new Identifier("x",localCounter,localCounter)
      }

      override def transform(id: Identifier): Identifier = {
        val visited = ids contains id
        val nid = ids.getOrElseUpdate(id, freshId())

        if ((syms.functions contains id) && !visited) {
          functions = transform(syms.functions(id)) +: functions
        } else if ((syms.sorts contains id) && !visited) {
          sorts = transform(syms.sorts(id)) +: sorts
        }

        nid
      }
    }

    val newVCBody = IdTransformer.transform(vc.condition)
    val newSyms = NoSymbols.withFunctions(functions).withSorts(sorts)

    (newSyms, newVCBody)
  }
}


object Canonization {
  def canonize(p: inox.Program { val trees: stainless.ast.Trees })(vc: verification.VC[p.trees.type]): 
                (p.trees.Symbols, p.trees.Expr)  = {
    object Canonizer extends Canonization {
      override val trees: p.trees.type = p.trees
    }

    val (newSymbols, newVCBody) = Canonizer.normalize(p.symbols, vc)

    (newSymbols, newVCBody)
  }
}
