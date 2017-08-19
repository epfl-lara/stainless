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

  def transform(syms: s.Symbols, vc: VC): (t.Symbols, Expr) = {

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

    // Map from old identifiers to new fundefs
    var transformedFunctions = Map[Identifier, FunDef]()
    // Map from old identifiers to new ADTs
    var transformedADTs = Map[Identifier, ADTDefinition]()

    object idTransformer extends inox.ast.TreeTransformer {
      val s: self.trees.type = self.trees
      val t: self.trees.type = self.trees

      var traversed = Set[Identifier]()

      def exploreFunDef(id: Identifier): Unit = {
        if (syms.functions.contains(id) && !traversed(id)) {
          traversed += id
          val fd = syms.functions(id)
          val newFD = transform(fd)
          transformedFunctions += ((id, newFD))
        }
      }

      def transformADT(adt: ADTDefinition): ADTDefinition = {
        val newInvariant = adt.invariant(syms) map transform
        transform(adt).changeInvariant(newInvariant)
      }

      def exploreADT(id: Identifier): Unit = {
        if (syms.adts.contains(id) && !traversed(id)) {
          traversed += id
          val adt = syms.adts(id)
          val newADT = transformADT(adt)
          transformedADTs += ((id, newADT))
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

    val newFundefs = syms.functions.values.map { fd => 
      // explore again in case this FunDef was not explored during the transformation of vc
      idTransformer.exploreFunDef(fd.id)         
      transformedFunctions(fd.id)
    }

    val newADTs = syms.adts.values.map { adt =>
      // explore again in case this ADT was not explored during the transformation of vc
      idTransformer.exploreADT(adt.id)
      transformedADTs(adt.id)
    }
    val newSyms = NoSymbols.withFunctions(newFundefs.toSeq).withADTs(newADTs.toSeq)

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