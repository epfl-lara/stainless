/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification


import java.io.ObjectInputStream
import java.io.FileInputStream
import java.io.ObjectOutputStream
import java.io.FileOutputStream

import inox.solvers.SolverFactory

object DebugSectionCacheHit extends inox.DebugSection("cachehit")
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

  val uniq = new PrinterOptions(printUniqueIds = true)

  override def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }) = {
    import VerificationCache._

    ctx.reporter.synchronized {
      ctx.reporter.info(s" - Checking cache: '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")
    }

    val canonic = transformers.Canonization.canonize(program)(vc)

    if (VerificationCache.contains(program.trees)(canonic)) {
      ctx.reporter.synchronized {
        ctx.reporter.info(s"Cache hit: '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")
        ctx.reporter.debug("The following VC has already been verified:")(DebugSectionCacheHit)
        ctx.reporter.debug(vc.condition)(DebugSectionCacheHit)
        ctx.reporter.debug("--------------")(DebugSectionCacheHit)
      }
      VCResult(VCStatus.ValidFromCache, None, Some(0))
    } else {
      ctx.reporter.synchronized {
        ctx.reporter.info(s"Cache miss: '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")
        ctx.reporter.debug("Cache miss for VC")(DebugSectionCacheMiss)
        ctx.reporter.debug(vc.condition)(DebugSectionCacheMiss)
        ctx.reporter.debug("Canonical form:")(DebugSectionCacheMiss)
        ctx.reporter.debug(serialize(program.trees)(canonic))(DebugSectionCacheMiss)
        ctx.reporter.debug("--------------")(DebugSectionCacheMiss)
      }
      val result = super.checkVC(vc,sf)
      if (result.isValid) {
        VerificationCache.add(program.trees)(canonic)
        VerificationCache.persist(program.trees)(canonic, vc.toString, ctx)
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
    val uniq = new tt.PrinterOptions(printUniqueIds = true, printTypes = true, symbols = Some(p._1))
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
        val s = serialize(tt)(p)
        VerificationCache.synchronized {
          oos.writeObject(s)
        }
        descr
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