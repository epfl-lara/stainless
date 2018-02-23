/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification


import java.io.File
import java.io.ObjectInputStream
import java.io.FileInputStream
import java.io.ObjectOutputStream
import java.io.FileOutputStream

import scala.collection.concurrent.TrieMap
import scala.util.{ Success, Failure }

import inox.solvers.SolverFactory

object DebugSectionCacheHit extends inox.DebugSection("cachehit")
object DebugSectionCacheMiss extends inox.DebugSection("cachemiss")

class AppendingObjectOutputStream(os: java.io.OutputStream) extends ObjectOutputStream(os) {
  override protected def writeStreamHeader() = {
    reset()
  }
}

/**
 * VerificationChecker with cache for VC results.
 *
 * NOTE Several instance of this trait can be created, but under the constraint that they
 *      all share the same [[inox.Context]] because the cache file is shared among all instances.
 */
trait VerificationCache extends VerificationChecker { self =>

  import context._
  import program._
  import program.symbols._
  import program.trees._

  override def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }) = {
    reporter.info(s" - Checking cache: '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")

    // NOTE This algorithm is not 100% perfect: it is possible that two equivalent VCs in
    //      the same program are both computed concurrently (contains return false twice),
    //      and both added to the cache. Assuming the VC result is always the same, the
    //      second result will override the first one in the cache without creating bugs.
    //      The cache file will also contain twice the same information, but it is expected
    //      that the even is rare enough and therefore will not result in huge cache files.

    val (time, tryResult) = timers.verification.cache.runAndGetTime {
      val canonic = transformers.Canonization.canonize(program)(vc)
      if (contains(canonic)) {
        reporter.synchronized {
          reporter.info(s"Cache hit: '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")
          reporter.debug("The following VC has already been verified:")(DebugSectionCacheHit)
          reporter.debug(vc.condition)(DebugSectionCacheHit)
          reporter.debug("--------------")(DebugSectionCacheHit)
        }
        VCResult(VCStatus.ValidFromCache, None, None)
      } else {
        reporter.synchronized {
          reporter.info(s"Cache miss: '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")
          reporter.debug("Cache miss for VC")(DebugSectionCacheMiss)
          reporter.debug(vc.condition)(DebugSectionCacheMiss)
          reporter.debug("Canonical form:")(DebugSectionCacheMiss)
          reporter.debug(serialize(canonic))(DebugSectionCacheMiss)
          reporter.debug("--------------")(DebugSectionCacheMiss)
        }

        val result = super.checkVC(vc,sf)
        if (result.isValid) {
          add(canonic)
        }

        result
      }
    }

    // Update the result with the correct processing time
    tryResult match {
      case Failure(e) => reporter.internalError(e)
      case Success(VCResult(status, solver, _)) => VCResult(status, solver, Some(time))
    }
  }

  private val cacheFile: File = utils.Caches.getCacheFile(context, "vccache.bin")
  private val vccache: Cache = CacheLoader.get(context, cacheFile)

  private def contains(p: (Symbols, Expr)) = vccache contains serialize(p)
  private def add(p: (Symbols, Expr)) = vccache addPersistently serialize(p)

  /**
    * Transforms the dependencies of a VC and a VC to a String
    * The functions and ADTs representations are sorted to avoid non-determinism
    */
  private def serialize(p: (Symbols, Expr)): String = {
    val uniq = new PrinterOptions(printUniqueIds = true, printTypes = true, symbols = Some(p._1))
    p._1.functions.values.map(fd => fd.asString(uniq)).toList.sorted.mkString("\n\n") +
    "\n#\n" +
    p._1.sorts.values.map(sort => sort.asString(uniq)).toList.sorted.mkString("\n\n") +
    "\n#\n" +
    p._2.asString(uniq)
  }

}

/** Cache with the ability to save itself to disk. */
private class Cache(cacheFile: File) {
  // API
  def contains(serialized: String): Boolean = underlying contains serialized
  def +=(serialized: String) = underlying += serialized -> unusedCacheValue
  def addPersistently(serialized: String): Unit = {
    this += serialized
    this.synchronized { oos writeObject serialized }
  }

  // Implementation details
  private val underlying = TrieMap[String, Unit]() // Thread safe
  private val unusedCacheValue = ()

  // output stream used to save verified VCs
  private val oos = if (cacheFile.exists) {
    new AppendingObjectOutputStream(new FileOutputStream(cacheFile, true))
  } else {
    new ObjectOutputStream(new FileOutputStream(cacheFile))
  }
}

/**
 * Only two tasks for the cache loader:
 *  - initialize the cache from the file,
 *  - return the same [[Cache]] instance for the same [[File]].
 */
private object CacheLoader {

  private val db = scala.collection.mutable.Map[File, Cache]()

  /**
   * Opens an ObjectInputStream and catches corruption errors
   */
  def openStream(ctx: inox.Context, file: File): ObjectInputStream = {
    try new ObjectInputStream(new FileInputStream(file))
    catch {
      case e: java.io.StreamCorruptedException =>
        ctx.reporter.fatalError(s"The cache file '$file' is corrupt. Please delete it.")
    }
  }

  /**
   * Closes an ObjectInputStream and catches potential IO errors
   */
  def closeStream(ctx: inox.Context, ois: ObjectInputStream, file: File) = {
    try ois.close()
    catch {
      case e: java.io.IOException =>
        ctx.reporter.error(s"Could not close ObjectInputStream of $file properly.")
    }
  }



  /**
   * Create a cache with the data stored in the given file if it exists.
   *
   * NOTE This function assumes the file is not written by another process
   *      while being loaded!
   */
  def get(ctx: inox.Context, cacheFile: File): Cache = this.synchronized {
    db.getOrElseUpdate(cacheFile, {
      val cache = new Cache(cacheFile)

      if (cacheFile.exists) {
        val ois = openStream(ctx, cacheFile)

        try {
          while (true) {
            val s = ois.readObject.asInstanceOf[String]
            cache += s
          }
        } catch {
          case e: java.io.EOFException => // Silently consume expected exception.
        } finally {
          closeStream(ctx,ois,cacheFile)
        }
      }

      cache
    })
  }

}

