/* Copyright 2009-2016 EPFL, Lausanne */

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

  // Sequence of transformed function definitions
  var functions = Seq[FunDef]()
  // Sequence of transformed ADT definitions
  var adts = Seq[ADTDefinition]()

  def transform(syms: s.Symbols, vc: VC): (t.Symbols, Expr) = {

    // Stores the transformed function and ADT definitions
    var functions = Seq[FunDef]()
    var adts = Seq[ADTDefinition]()

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
        } else if ((syms.adts contains id) && !visited) {
          adts = transform(syms.adts(id)) +: adts
        }

        nid
      }
    }

    val newVCBody = IdTransformer.transform(vc.condition)
    val newSyms = NoSymbols.withFunctions(functions).withADTs(adts)

    (newSyms, newVCBody)
  }
}


object Canonization {
  def canonize(trs: stainless.ast.Trees)
              (p: inox.Program { val trees: trs.type }, vc: verification.VC[trs.type]): 
                (p.trees.Symbols, trs.Expr)  = {
    object canonizer extends Canonization {
      override val trees: p.trees.type = p.trees
    }

    val (newSymbols, newVCBody) = canonizer.transform(p.symbols, vc)

    (newSymbols, newVCBody)
  }
}