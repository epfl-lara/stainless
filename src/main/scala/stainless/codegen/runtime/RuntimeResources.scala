/* Copyright 2009-2016 EPFL, Lausanne */

package leon.codegen.runtime

import leon.utils.UniqueCounter

import java.util.WeakHashMap
import java.lang.ref.WeakReference

/**
 * This class allows an evaluator to statically register a resource, identified
 * by an integer. This identifier can be stored in bytecode, allowing .class to
 * access the resource at runtime.
 *
 * The user/evaluator should keep hold of the returned Token, otherwise the
 * resource may be garbage-collected.
 *
 * This is not statically-typed, but
 *
 *   get[A]( register[A]( ... ) )
 *
 *  should always be safe.
 */
object RuntimeResources {
  case class Token(id: Int)

  private val intCounter = new UniqueCounter[Unit]

  private[this] val store = new WeakHashMap[Token, WeakReference[AnyRef]]()

  def register[T <: AnyRef](data: T): Token = synchronized {
    val t = Token(intCounter.nextGlobal)

    store.put(t, new WeakReference(data))

    t
  }

  def get[T <: AnyRef](id: Int): T = {
    store.get(Token(id)).get.asInstanceOf[T]
  }
}
