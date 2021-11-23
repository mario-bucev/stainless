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
   * Get the cache file after creating the cache directory.
   *
   * The cache file itself is not created. Return None when the switch if off.
   */
  def getCacheFile(ctx: inox.Context, optCacheSwitch: inox.FlagOptionDef, filename: String): Option[File] = {
    val cacheEnabled = ctx.options findOptionOrDefault optCacheSwitch
    if (cacheEnabled) Some(getCacheFile(ctx, filename)) else None
  }

  /**
   * Get the cache file after creating the cache directory and its subdirectory [[subdir]].
   *
   * The cache file itself is not created. Return None when the switch if off.
   */
  def getCacheFile(ctx: inox.Context, optCacheSwitch: inox.FlagOptionDef, subdir: String, filename: String): Option[File] =
    getCacheFile(ctx, optCacheSwitch, subdir) map { getSubFile(_, filename) }

  /**
   * Get the cache file after creating the cache directory.
   *
   * The cache file itself is not created.
   */
  def getCacheFile(ctx: inox.Context, filename: String): File = {
    val cacheDir = ctx.options.findOptionOrDefault(optCacheDir).getAbsoluteFile
    getSubFile(cacheDir, filename)
  }

  def getCacheSubdir(ctx: inox.Context, subdirName: String): File = {
    val cacheDir = ctx.options.findOptionOrDefault(optCacheDir).getAbsoluteFile
    val subdir = new File(cacheDir, subdirName)
    subdir.mkdirs()
    subdir
  }

  private def getSubFile(dir: File, filename: String): File = {
    dir.mkdirs()
    assert(dir.isDirectory, s"Not a directory: ${dir.getAbsolutePath}")
    new File(dir, filename)
  }
}

