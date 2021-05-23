/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package utils

import java.io.File

/** A wrapper around a byte array that provides valid equality and hashCode functions.
  * This class is useful for implementing caches based on efficient binary representations
  * of the cache keys. */
class Bytes(val bytes: Array[Byte]) {
  override def equals(that: Any): Boolean = that match {
    case b: Bytes => java.util.Arrays.equals(bytes, b.bytes)
    case _ => false
  }

  override val hashCode: Int = java.util.Arrays.hashCode(bytes)
}

object Bytes {
  def apply(bytes: Array[Byte]) = new Bytes(bytes)
}

object Caches {

  /** Caches used by stainless' components are stored in the same directory, denoted by this option. */
  object optCacheDir extends FileOptionDef {
    val name = "cache-dir"
    val default = new File(".stainless-cache/")
    override val usageRhs = "DIR"
  }

  /**
   * Get the cache directory, and create it if necessary.
   *
   * Return None when the switch if off.
   */
  def getCacheDir(ctx: inox.Context, optCacheSwitch: inox.FlagOptionDef): Option[File] = {
    val cacheEnabled = ctx.options findOptionOrDefault optCacheSwitch
    if (cacheEnabled) Some(getCacheDir(ctx)) else None
  }

  /**
   * Get the cache directory, creating it if necessary.
   */
  def getCacheDir(ctx: inox.Context): File = {
    val cacheDir = ctx.options.findOptionOrDefault(optCacheDir).getAbsoluteFile
    cacheDir.mkdirs()
    cacheDir
  }
}

