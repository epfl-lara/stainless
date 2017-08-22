/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

import stainless.extraction.inlining.Trees

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

    object idTransformer extends inox.ast.TreeTransformer {
      val s: self.trees.type = self.trees
      val t: self.trees.type = self.trees

      var localCounter = 0
      // Maps an original identifier to a normalized identifier
      var renaming: Map[Identifier,Identifier] = Map()

      def addRenaming(id: Identifier): Unit = {
        if (!renaming.contains(id)) {
          val newId = new Identifier("x",localCounter,localCounter)
          localCounter = localCounter + 1
          renaming += ((id, newId))
        }
      }

      var traversed = Set[Identifier]()

      def exploreFunDef(id: Identifier): Unit = {
        if (syms.functions.contains(id) && !traversed(id)) {
          traversed += id
          val fd = syms.functions(id)
          val newFD = transform(fd)
          functions :+= newFD
        }
      }

      def exploreADT(id: Identifier): Unit = {
        if (syms.adts.contains(id) && !traversed(id)) {
          traversed += id
          val adt = syms.adts(id)
          val newADT = transform(adt)
          adts :+= newADT
        }
      }

      override def transform(id: Identifier): Identifier = {
        addRenaming(id)
        exploreFunDef(id)
        exploreADT(id)
        renaming(id)
      }
    }

    val newVCBody = idTransformer.transform(vc.condition)

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