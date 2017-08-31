/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package utils

import java.io.File

object Caches {

  /** Caches used by stainless' components are stored in the same directory, denoted by this option. */
  object optCacheDir extends inox.OptionDef[String] {
    val name = "cache-dir"
    val default = "cache/"
    val parser = inox.OptionParsers.stringParser
    val usageRhs = "directory"
  }

  /**
   * Get the cache file after creating the cache directory.
   *
   * The cache file itself is not created. Return None when the switch if off.
   */
  def getCacheFile(ctx: inox.Context, optCacheSwitch: inox.FlagOptionDef, cacheFilename: String): Option[File] = {
    if (ctx.options findOptionOrDefault optCacheSwitch) Some(getCacheFile(ctx, cacheFilename))
    else None
  }

  /**
   * Get the cache file after creating the cache directory.
   *
   * The cache file itself is not created.
   */
  def getCacheFile(ctx: inox.Context, cacheFilename: String): File = {
    val dir = new File(ctx.options findOptionOrDefault optCacheDir).getAbsoluteFile
    dir.mkdirs()
    assert(dir.isDirectory)
    new File(dir, cacheFilename)
  }

}

