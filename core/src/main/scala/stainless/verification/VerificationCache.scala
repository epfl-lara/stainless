/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification


import java.io.File
import java.io.InputStream
import java.io.OutputStream
import java.io.FileInputStream
import java.io.FileOutputStream

import scala.collection.concurrent.TrieMap
import scala.util.{ Success, Failure }

import inox.solvers.SolverFactory

object DebugSectionCacheHit extends inox.DebugSection("cachehit")
object DebugSectionCacheMiss extends inox.DebugSection("cachemiss")

/**
 * VerificationChecker with cache for VC results.
 *
 * NOTE Several instance of this trait can be created, but under the constraint that they
 *      all share the same [[inox.Context]] because the cache file is shared among all instances.
 */
trait VerificationCache extends VerificationChecker { self =>
  val program: StainlessProgram

  import context.{given, _}
  import program._
  import program.symbols.{given, _}
  import program.trees._

  import VerificationCache._
  import serializer._

  private lazy val vccache = CacheLoader.get(context)

  override def checkVC(vc: VC, origVC: VC, sf: SolverFactory { val program: self.program.type }) = {
    reporter.debug(s" - Checking cache: '${vc.kind}' VC for ${vc.fid} @${vc.getPos}...")(using DebugSectionVerification)

    // NOTE This algorithm is not 100% perfect: it is possible that two equivalent VCs in
    //      the same program are both computed concurrently (contains return false twice),
    //      and both added to the cache. Assuming the VC result is always the same, the
    //      second result will override the first one in the cache without creating bugs.
    //      The cache file will also contain twice the same information, but it is expected
    //      that the event is rare enough and therefore will not result in huge cache files.

    val (time, tryResult) = timers.verification.cache.runAndGetTime {
      val (canonicalSymbols, canonicalExpr): (Symbols, Expr) =
        utils.Canonization(program)(program.symbols, vc.condition)

      val key = serializer.serialize((vc.satisfiability, canonicalSymbols, canonicalExpr))

      if (vccache contains key) {
        reporter.debug(s"Cache hit: '${vc.kind}' VC for ${vc.fid.asString} @${vc.getPos}...")(using DebugSectionVerification)
        given DebugSectionCacheHit.type = DebugSectionCacheHit
        reporter.synchronized {
          reporter.debug("The following VC has already been verified:")
          debugVC(vc, origVC)
          reporter.debug("--------------")
        }
        VCResult(VCStatus.ValidFromCache, None, None)
      } else {
        reporter.synchronized {
          reporter.debug(s"Cache miss: '${vc.kind}' VC for ${vc.fid.asString} @${vc.getPos}...")
          reporter.ifDebug { debug =>
            given DebugSectionCacheMiss.type = DebugSectionCacheMiss
            given PrinterOptions = new PrinterOptions(printUniqueIds = true, printTypes = true, symbols = Some(canonicalSymbols))

            debugVC(vc, origVC)

            debug("Canonical symbols:")
            debug(" ## SORTS ##")
            debug(canonicalSymbols.sorts.values.map(_.asString).toList.sorted.mkString("\n\n"))
            debug(" ## FUNCTIONS ##")
            debug(canonicalSymbols.functions.values.map(_.asString).toList.sorted.mkString("\n\n"))
            debug("Canonical verification condition:")
            debug(canonicalExpr)
            debug("--------------")
          } (using DebugSectionCacheMiss)
        }

        val result = super.checkVC(vc, origVC, sf)
        if (result.isValid) {
          vccache addPersistently key
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
}

object VerificationCache {
  private val serializer = utils.Serializer(stainless.trees)
  import serializer.{given, _}

  /** Cache with the ability to save itself to disk. */
  private class Cache(cacheFile: File) {
    // API
    def contains(key: SerializationResult): Boolean = underlying contains key
    def +=(key: SerializationResult) = underlying += key -> unusedCacheValue
    def addPersistently(key: SerializationResult): Unit = {
      this += key
      this.synchronized { serializer.serialize(key, out) }
    }

    // Implementation details
    private val underlying = TrieMap[SerializationResult, Unit]() // Thread safe
    private val unusedCacheValue = ()

    // output stream used to save verified VCs
    private val out =
      if (cacheFile.exists) new FileOutputStream(cacheFile, true)
      else new FileOutputStream(cacheFile)
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
    private def openStream(ctx: inox.Context, file: File): InputStream = {
      try new FileInputStream(file)
      catch {
        case e: java.io.FileNotFoundException =>
          ctx.reporter.fatalError(s"Could not open cache file at $file.")
      }
    }

    /**
     * Closes an ObjectInputStream and catches potential IO errors
     */
    private def closeStream(ctx: inox.Context, in: InputStream, file: File) = {
      try in.close()
      catch {
        case e: java.io.IOException =>
          ctx.reporter.error(s"Could not close InputStream of $file properly.")
      }
    }



    /**
     * Create a cache with the data stored in the given file if it exists.
     *
     * NOTE This function assumes the file is not written by another process
     *      while being loaded!
     */
    def get(ctx: inox.Context): Cache = this.synchronized {
      val cacheFile: File = utils.Caches.getCacheFile(ctx, "vccache.bin")

      db.getOrElse(cacheFile, {
        val cache = new Cache(cacheFile)

        if (cacheFile.exists) {
          val in = openStream(ctx, cacheFile)

          try {
            while (true) {
              val s = serializer.deserialize[SerializationResult](in)
              cache += s
            }
          } catch {
            case e: java.io.EOFException => // Silently consume expected exception.
          } finally {
            closeStream(ctx, in, cacheFile)
          }
        }

        db(cacheFile) = cache
        cache
      })
    }
  }
}

