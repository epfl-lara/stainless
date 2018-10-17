/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

trait ExtractionCaches { self: ExtractionContext =>

  /** A super type for all cache keys.
    * The set of dependencies is required in order to invalidate cache entries. */
  protected abstract class CacheKey {
    def dependencies: Set[Identifier]

    /* Ordered key union, useful for multi-key dependencies. */
    def +(that: CacheKey) = new SeqKey(Seq(this, that))
  }

  /** A super type for all cache key generators.
    * This typeclass is used for instantiating extraction caches by key type. */
  protected abstract class Keyable[T] { 
    def apply(key: T): CacheKey 
  }


  private final class FunctionKey private(private val fd: s.FunDef) extends CacheKey {
    override def dependencies = Set(fd.id)

    // We can't use the `FunDef` as a key directly here as its equality is
    // overriden to only consider the `id`, which is insufficient for our
    // caching needs as we maintain identifiers regardless of transformations
    private val key = (
      fd.id,
      fd.typeArgs,
      fd.params.map(_.toVariable),
      fd.returnType,
      fd.fullBody,
      fd.flags
    )

    override def hashCode: Int = key.hashCode
    override def equals(that: Any): Boolean = that match {
      case fk: FunctionKey => (fd eq fk.fd) || (key == fk.key)
      case _ => false
    }

    override def toString: String = s"FunctionKey(${fd.id.asString})"
  }

  protected implicit object FunctionKey extends Keyable[s.FunDef] {
    def apply(id: Identifier)(implicit symbols: s.Symbols): CacheKey = apply(symbols.getFunction(id))
    def apply(fd: s.FunDef): CacheKey = new FunctionKey(fd)
  }

  private final class SortKey private(private val sort: s.ADTSort) extends CacheKey {
    override def dependencies = Set(sort.id)

    // We again can't use the `ADTSort` as a key for the same reasons as exposed
    // in the `FunctionKey` case.
    private val key = (
      sort.id,
      sort.typeArgs,
      sort.constructors.map { cons =>
        (cons.id, cons.sort, cons.fields.map(_.toVariable))
      }
    )

    override def hashCode: Int = key.hashCode
    override def equals(that: Any): Boolean = that match {
      case sk: SortKey => (sort eq sk.sort) || (key == sk.key)
      case _ => false
    }

    override def toString: String = s"SortKey(${sort.id.asString})"
  }

  protected implicit object SortKey extends Keyable[s.ADTSort] {
    def apply(id: Identifier)(implicit symbols: s.Symbols): CacheKey = apply(symbols.getSort(id))
    def apply(sort: s.ADTSort): CacheKey = new SortKey(sort)
  }

  /** Returns a [[SimpleKey]] given some identifier and the symbols from which
    * it was taken.
    *
    * This is an override point for [[ExtractionCaches]] sub-classes where symbols
    * may contain different definitions (such as class definitions). */
  protected def getSimpleKey(id: Identifier)(implicit symbols: s.Symbols): CacheKey =
    symbols.lookupFunction(id).map(FunctionKey(_))
      .orElse(symbols.lookupSort(id).map(SortKey(_)))
      .getOrElse(throw new RuntimeException(
        "Couldn't find symbol " + id.asString + " in symbols\n\n" + symbols.asString))

  /** Returns a [[CacheKey]] given some identifier and the symbols from which
    * it was taken (uses `symbols.dependencies` to compute the set of dependencies). */
  protected def getDependencyKey(id: Identifier)(implicit symbols: s.Symbols): CacheKey =
    getSimpleKey(id) + SetKey(symbols.dependencies(id))


  /** A [[CacheKey]] that simply composes a sequence of sub-keys. */
  protected sealed class SeqKey(private val keys: Seq[CacheKey]) extends CacheKey {
    override val dependencies = keys.flatMap(_.dependencies).toSet

    override def hashCode: Int = keys.hashCode
    override def equals(that: Any): Boolean = that match {
      case uk: SeqKey => keys == uk.keys
      case _ => false
    }

    override def toString: String = s"SeqKey(${keys.mkString(", ")})"
  }

  object SeqKey {
    def apply(keys: Seq[CacheKey]) = new SeqKey(keys)
  }

  /** A [[CacheKey]] that simply composes a set of sub-keys. */
  protected sealed class SetKey(private val keys: Set[CacheKey]) extends CacheKey {
    override val dependencies = keys.flatMap(_.dependencies)

    override def hashCode: Int = keys.hashCode
    override def equals(that: Any): Boolean = that match {
      case uk: SetKey => keys == uk.keys
      case _ => false
    }

    override def toString: String = s"SetKey(${keys.mkString(", ")})"
  }

  object SetKey {
    def apply(keys: Set[CacheKey]): SetKey = new SetKey(keys)
    def apply(ids: Set[Identifier])(implicit syms: s.Symbols): SetKey =
      SetKey(ids.map(getSimpleKey))
    def apply[T: Keyable](elems: Set[T]): SetKey = {
      val gen = implicitly[Keyable[T]]
      SetKey(elems.map(gen.apply))
    }
  }


  /** A [[CacheKey]] that relies on the equality of the underlying value.
    * Note that the value should not contain any definitions as they will
    * not register as dependencies of this key! */
  protected sealed class ValueKey[T](private val value: T) extends CacheKey {
    override def dependencies = Set()

    override def hashCode: Int = value.hashCode
    override def equals(that: Any): Boolean = that match {
      case (vk: ValueKey[_]) => value == vk.value
      case _ => false
    }

    override def toString: String = s"ValueKey($value)"
  }

  object ValueKey {
    def apply[T](value: T) = new ValueKey(value)
  }

  private[this] val caches =
    new scala.collection.mutable.ListBuffer[ExtractionCache[_, _]]

  /** An extraction cache that gets added to the collection `caches`.
    * Can be invalidated from specific identifiers */
  protected sealed class ExtractionCache[A, B](gen: (A,TransformerContext) => CacheKey) {
    val cache = new utils.ConcurrentCache[CacheKey, B]

    def cached(key: A, c: TransformerContext)(builder: => B): B = cache.cached(gen(key, c))(builder)
    def contains(key: A, c: TransformerContext): Boolean = cache contains gen(key, c)
    def update(key: A, c: TransformerContext, value: B): Unit = cache.update(gen(key, c), value)
    def get(key: A, c: TransformerContext): Option[B] = cache.get(gen(key, c))
    def apply(key: A, c: TransformerContext): B = cache(gen(key, c))


    def invalidate(id: Identifier): Unit =
      this.cache.retain(key => !(key.dependencies contains id))

    self.synchronized(caches += this)
  }

  /** A simple extraction cache that ignores the `TransformerContext` */
  protected final class SimpleCache[A: Keyable, B] extends ExtractionCache[A, B](
    (a, _) => implicitly[Keyable[A]].apply(a)
  ) {
    val gen = implicitly[Keyable[A]]
    def cached(key: A)(builder: => B): B = cache.cached(gen(key))(builder)
    def contains(key: A): Boolean = cache contains gen(key)
    def update(key: A, value: B): Unit = cache.update(gen(key), value)
    def get(key: A): Option[B] = cache.get(gen(key))
    def apply(key: A): B = cache(gen(key))
  }

  override def invalidate(id: Identifier): Unit = {
    for (cache <- caches) cache.invalidate(id)
  }
}
