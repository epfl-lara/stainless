/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification


import java.io.ObjectInputStream
import java.io.FileInputStream
import java.io.ObjectOutputStream
import java.io.FileOutputStream

import inox.solvers.SolverFactory

object DebugSectionCache extends inox.DebugSection("vccache")
object DebugSectionCacheMiss extends inox.DebugSection("cachemiss")

class AppendingObjectOutputStream(os: java.io.OutputStream) extends ObjectOutputStream(os) {
  override protected def writeStreamHeader() = {
    reset()
  }
}

trait VerificationCache extends VerificationChecker { self =>

  import program._
  import program.symbols._
  import program.trees._

  type SubProgram = inox.Program { val trees: program.trees.type }

  val uniq = new PrinterOptions(printUniqueIds = true)

  def buildDependencies(vc: VC): SubProgram = {

    var adts = Set[ADTDefinition]()
    var fundefs = Set[FunDef]()
    var traversed = Set[Identifier]()

    val traverser = new TreeTraverser {
      override def traverse(id: Identifier): Unit = {
        if (!traversed.contains(id)) {
          traversed += id
          if (program.symbols.functions.contains(id)) {
            val fd = program.symbols.functions(id)
            fundefs += fd
            traverse(fd)
          }
          else if (program.symbols.adts.contains(id)) {
            val adtdef = program.symbols.adts(id)
            adts += adtdef
            fundefs ++= adtdef.invariant
            traverse(adtdef)
            adtdef.invariant foreach traverse
          }
        }
      }
    }

    traverser.traverse(vc.condition)

    new inox.Program {
      val trees: program.trees.type = program.trees
      val symbols = NoSymbols.withFunctions(fundefs.toSeq).withADTs(adts.toSeq)
      val ctx = program.ctx
    }
  }

  override def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }) = {
    import VerificationCache._

    val sp: SubProgram = buildDependencies(vc)
    val canonic = transformers.Canonization.canonize(sp.trees)(sp, vc)
    if (VerificationCache.contains(sp.trees)(canonic)) {
      ctx.reporter.synchronized {
        ctx.reporter.debug("The following VC has already been verified:")(DebugSectionCache)
        ctx.reporter.debug(vc.condition)(DebugSectionCache)
        ctx.reporter.debug("--------------")(DebugSectionCache)
      }
      VCResult(VCStatus.Valid, None, Some(0))
    }
    else {
      ctx.reporter.synchronized {
        ctx.reporter.debug("Cache miss:")(DebugSectionCacheMiss)
        ctx.reporter.debug(serialize(sp.trees)(canonic))(DebugSectionCacheMiss)
        ctx.reporter.debug("--------------")(DebugSectionCacheMiss)
      }
      val result = super.checkVC(vc,sf)
      VerificationCache.add(sp.trees)(canonic)
      VerificationCache.addVCToPersistentCache(sp.trees)(canonic, vc.toString, ctx)
      result
    }
  }

}

object VerificationCache {
  val cacheFile = ".vccache.bin"
  var vccache = scala.collection.concurrent.TrieMap[String,Unit]()
  VerificationCache.loadPersistentCache()
  
  // output stream used to save verified VCs 
  val oos = if (new java.io.File(cacheFile).exists) {
    new AppendingObjectOutputStream(new FileOutputStream(cacheFile, true))
  } else {
    new ObjectOutputStream(new FileOutputStream(cacheFile))
  }
    
  def contains(tt: inox.ast.Trees)(p: (tt.Symbols, tt.Expr)) = {
    vccache.contains(serialize(tt)(p))
  }
    
  def add(tt: inox.ast.Trees)(p: (tt.Symbols, tt.Expr)) = {
    vccache += ((serialize(tt)(p), ()))
  }

  /**
    * Transforms the dependencies of a VC and a VC to a String
    * The functions and ADTs representations are sorted to avoid non-determinism
    */
  def serialize(tt: inox.ast.Trees)(p: (tt. Symbols, tt. Expr)): String = {
    val uniq = new tt.PrinterOptions(printUniqueIds = true)
    p._1.functions.values.map(fd => fd.asString(uniq)).toList.sorted.mkString("\n\n") + 
    "\n#\n" + 
    p._1.adts.values.map(adt => adt.asString(uniq)).toList.sorted.mkString("\n\n") + 
    "\n#\n" + 
    p._2.asString(uniq)
  }

  def addVCToPersistentCache(tt: inox.ast.Trees)(p: (tt. Symbols, tt. Expr), descr: String, ctx: inox.Context): Unit = {

    val task = new java.util.concurrent.Callable[String] {
      override def call(): String = {
        MainHelpers.synchronized {
          oos.writeObject(serialize(tt)(p))
          descr
        }
      }
    }
    MainHelpers.executor.submit(task)
  }
  
  def loadPersistentCache(): Unit = {
    if (new java.io.File(cacheFile).exists) {
      MainHelpers.synchronized {
        val ois = new ObjectInputStream(new FileInputStream(cacheFile))
        try {
          while (true) {
            val s = ois.readObject.asInstanceOf[String]
            vccache += ((s, ()))
          }
        } catch {
          case e: java.io.EOFException => ois.close()
        }
      }
    }
  }

}