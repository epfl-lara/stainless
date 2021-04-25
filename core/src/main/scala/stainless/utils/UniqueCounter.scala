/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.utils

class UniqueCounter[K] {

  private var globalId = -1
  private var nameIds = Map[K, Int]().withDefaultValue(-1)

  def next(key: K): Int = synchronized {
    nameIds += key -> (1+nameIds(key))
    nameIds(key)
  }

  def nextGlobal = synchronized {
    globalId += 1
    globalId
  }

  def current = nameIds
}
