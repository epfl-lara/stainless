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

// For Hashing
import java.security.MessageDigest
import java.util.HexFormat

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

  private val binaryCacheFlag = context.options.findOptionOrDefault(utils.Caches.optBinaryCache)

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


      val serialized = serializer.serialize((vc.satisfiability, canonicalSymbols, canonicalExpr))

      val key: CacheKey = vccache.computeKey(serialized.bytes)
      reporter.debug(s"Cache key size: ${key.content.size} bytes")(using DebugSectionVerification)
      if (vccache.contains(key)) {
        reporter.debug(s"Cache hit: '${vc.kind}' VC for ${vc.fid.asString} @${vc.getPos}...")(using DebugSectionVerification)
        given DebugSectionCacheHit.type = DebugSectionCacheHit
        reporter.synchronized {
          reporter.debug("The following VC has already been verified:")
          debugVC(vc, origVC)
          reporter.debug("--------------")
        }
        VCResult(VCStatus.ValidFromCache, None, None, None)
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
        if (result.isValid && vc.condition != BooleanLiteral(true)) {
          vccache `addPersistently` key
        }

        result
      }
    }

    // Update the result with the correct processing time
    tryResult match {
      case Failure(e) => reporter.internalError(e)
      case Success(VCResult(status, solver, _, smtLibFileId)) => VCResult(status, solver, Some(time), smtLibFileId)
    }
  }
}

object VerificationCache {
  private val serializer = utils.Serializer(stainless.trees)
  import serializer.{given, _}

  object CacheKey{
    def apply(content: Seq[Byte]): CacheKey = CacheKey(content.toArray)
  }
  case class CacheKey(content: Array[Byte]){
    override def equals(that: Any): Boolean = that match {
      case c: CacheKey => java.util.Arrays.equals(content, c.content)
      case _ => false
    }
    override val hashCode: Int = java.util.Arrays.hashCode(content)

    def toSeq: Seq[Byte] = content.toSeq
  }

  /** Cache with the ability to save itself to disk. */
  private class Cache(ctx: inox.Context, cacheFile: File) {
    val hashingFunctionName = "SHA-256"
    val hashSize = MessageDigest.getInstance(hashingFunctionName).getDigestLength()
    val hashCache = !ctx.options.findOptionOrDefault(utils.Caches.optBinaryCache)

    // API
    def computeKey(content: Array[Byte]): CacheKey = 
      if(hashCache) {
        val bytes = MessageDigest.getInstance(hashingFunctionName).digest(content)
        CacheKey(bytes)
      } else {
        CacheKey(content)
      }
    def contains(key: CacheKey): Boolean = underlying.contains(key)
    def +=(key: CacheKey) = underlying += key -> unusedCacheValue
    def addPersistently(key: CacheKey): Unit = {
      this += key
      this.synchronized { CacheKeySerializer.serialize(key, out) }
    }

    object CacheKeySerializer {
      def serialize(key: CacheKey, out: OutputStream): Unit = {
        if(hashCache){
          assert(key.content.size == hashSize)
          out.write(key.content)
        } else {
          serializer.serialize(key.toSeq, out)
        }
      }

      def deserialize(in: InputStream): CacheKey = {
        if(hashCache){
          val bytes = new Array[Byte](hashSize)
          if (in.available() < hashSize) throw new java.io.EOFException()
          in.read(bytes)
          CacheKey(bytes)
        } else {
          CacheKey(serializer.deserialize[Seq[Byte]](in))
        }
      }
    }

    // Implementation details
    private val underlying = TrieMap[CacheKey, Unit]() // Thread safe
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
      val cacheFile: File = utils.Caches.getCacheFile(ctx, utils.Caches.getCacheFilename(ctx))

      db.getOrElse(cacheFile, {
        val cache = new Cache(ctx, cacheFile)

        if (cacheFile.exists) {
          val in = openStream(ctx, cacheFile)

          try {
            while (true) {
              val ck = cache.CacheKeySerializer.deserialize(in)
              cache += ck
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

