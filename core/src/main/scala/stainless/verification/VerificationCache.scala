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

  /**
    * Builds the dependencies of a verification condition.
    * The dependencies are functions and ADT definitions, and form a program.
    */
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
          } else if (program.symbols.adts.contains(id)) {
            val adtdef = program.symbols.adts(id)
            adts += adtdef
            traverse(adtdef)
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
      if (result.isValid) {
        VerificationCache.add(sp.trees)(canonic)
        VerificationCache.persist(sp.trees)(canonic, vc.toString, ctx)
      }
      result
    }
  }

}

object VerificationCache {
  private val cacheFile = ".vccache.bin"
  private var vccache = scala.collection.concurrent.TrieMap[String,Unit]()
  VerificationCache.loadPersistentCache()
  
  // output stream used to save verified VCs 
  private val oos = if (new java.io.File(cacheFile).exists) {
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
  def serialize(tt: inox.ast.Trees)(p: (tt.Symbols, tt.Expr)): String = {
    val uniq = new tt.PrinterOptions(printUniqueIds = true)
    p._1.functions.values.map(fd => fd.asString(uniq)).toList.sorted.mkString("\n\n") + 
    "\n#\n" + 
    p._1.adts.values.map(adt => adt.asString(uniq)).toList.sorted.mkString("\n\n") + 
    "\n#\n" + 
    p._2.asString(uniq)
  }

  /**
    * Creates a task that adds a VC (and its dependencies) to the cache file
    */
  def persist(tt: inox.ast.Trees)(p: (tt.Symbols, tt.Expr), descr: String, ctx: inox.Context): Unit = {

    val task = new java.util.concurrent.Callable[String] {
      override def call(): String = {
        VerificationCache.synchronized {
          oos.writeObject(serialize(tt)(p))
          descr
        }
      }
    }
    MainHelpers.executor.submit(task)
  }
  
  /**
    * Loads all the VCs stored in the cache file and puts them in the
    * `vccache` map.
    */
  private def loadPersistentCache(): Unit = {
    if (new java.io.File(cacheFile).exists) {
      VerificationCache.synchronized {
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