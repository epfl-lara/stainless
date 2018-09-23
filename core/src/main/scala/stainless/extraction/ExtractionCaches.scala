/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

trait ExtractionCaches { self: ExtractionPipeline =>

  /** A super type for all cache keys.
    * The set of dependencies is required in order to invalidate cache entries. */
  protected abstract class CacheKey {
    def dependencies: Set[Identifier]

    /* Ordered key union, useful for multi-key dependencies. */
    def +(that: CacheKey) = new SeqKey(Seq(this, that))
  }

  /** A super type for all cache key generators.
    * This typeclass is used for instantiating extraction caches by key type. */
  protected sealed abstract class Keyable[T] { def apply(key: T, symbols: s.Symbols): CacheKey }


  /** A super type of cache keys that don't consider symbol dependencies. */
  protected abstract class SimpleKey extends CacheKey

  /** A super type for all simple cache key generators. */
  protected abstract class SimpleKeyable[T] extends Keyable[T] {
    override def apply(key: T, symbols: s.Symbols): SimpleKey
  }

  private final class FunctionKey private(private val fd: s.FunDef) extends SimpleKey {
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

  protected implicit object FunctionKey extends SimpleKeyable[s.FunDef] {
    override def apply(fd: s.FunDef, symbols: s.Symbols): SimpleKey = new FunctionKey(fd)
  }

  private final class SortKey private(private val sort: s.ADTSort) extends SimpleKey {
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

  protected implicit object SortKey extends SimpleKeyable[s.ADTSort] {
    override def apply(sort: s.ADTSort, symbols: s.Symbols): SimpleKey = new SortKey(sort)
  }


  /** Returns a [[SimpleKey]] given some identifier and the symbols from which
    * it was taken.
    *
    * This is an override point for [[ExtractionCaches]] sub-classes where symbols
    * may contain different definitions (such as class definitions). */
  protected def getSimpleKey(id: Identifier)(implicit symbols: s.Symbols): SimpleKey =
    symbols.lookupFunction(id).map(FunctionKey(_, symbols))
      .orElse(symbols.lookupSort(id).map(SortKey(_, symbols)))
      .getOrElse(throw new RuntimeException(
        "Couldn't find symbol " + id.asString + " in symbols " + symbols.asString))


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


  /** A [[CacheKey]] that relies on a set of _dependent_ keys for equality. */
  protected class DependencyKey(private val id: Identifier, private val keys: Set[CacheKey]) extends CacheKey {
    override val dependencies = keys.flatMap(_.dependencies) + id

    def this(id: Identifier)(implicit symbols: s.Symbols) =
      this(id, (symbols.dependencies(id) + id).map(getSimpleKey(_)): Set[CacheKey])

    def this(id: Identifier, dependencies: Set[Identifier])(implicit symbols: s.Symbols) =
      this(id, (dependencies + id).map(getSimpleKey(_)): Set[CacheKey])

    override def hashCode: Int = (id, keys).hashCode
    override def equals(that: Any): Boolean = that match {
      case dk: DependencyKey => id == dk.id && keys == dk.keys
      case _ => false
    }

    override def toString: String = s"DependencyKey($id, ${keys.mkString(", ")})"
  }

  /** A super type for all dependency cache key generators. */
  protected abstract class DependencyKeyable[T] extends Keyable[T] {
    override def apply(key: T, symbols: s.Symbols): DependencyKey
  }


  private final class FunctionDependencyKey private(fd: s.FunDef)(implicit symbols: s.Symbols)
    extends DependencyKey(fd.id)(symbols)

  protected implicit object FunctionDependencyKey extends DependencyKeyable[s.FunDef] {
    override def apply(fd: s.FunDef, symbols: s.Symbols): DependencyKey = new FunctionDependencyKey(fd)(symbols)
  }

  private final class SortDependencyKey private(sort: s.ADTSort)(implicit symbols: s.Symbols)
    extends DependencyKey(sort.id)(symbols)

  protected implicit object SortDependencyKey extends DependencyKeyable[s.ADTSort] {
    override def apply(sort: s.ADTSort, symbols: s.Symbols): DependencyKey = new SortDependencyKey(sort)(symbols)
  }

  /** Returns a [[DependencyKey]] given some identifier and the symbols from which
    * it was taken (uses `symbols.dependencies` to compute the set of dependencies).
    *
    * This is an override point for [[ExtractionCaches]] sub-classes where symbols
    * may contain different definitions (such as class definitions). */
  protected def getDependencyKey(id: Identifier)(implicit symbols: s.Symbols): DependencyKey =
    symbols.lookupFunction(id).map(FunctionDependencyKey(_, symbols))
      .orElse(symbols.lookupSort(id).map(SortDependencyKey(_, symbols)))
      .getOrElse(throw new RuntimeException(
        "Couldn't find symbol " + id.asString + " in symbols " + symbols.asString))


  private[this] val caches = new scala.collection.mutable.ListBuffer[ExtractionCache[_, _]]

  protected sealed class ExtractionCache[A: Keyable, B] protected[ExtractionCaches]() {
    private[this] final val keyable = implicitly[Keyable[A]]
    private[this] final val cache = new utils.ConcurrentCache[CacheKey, B]

    def cached(key: A, symbols: s.Symbols)(builder: => B): B = cache.cached(keyable(key, symbols))(builder)

    def contains(key: A, symbols: s.Symbols): Boolean = cache contains keyable(key, symbols)
    def update(key: A, symbols: s.Symbols, value: B): Unit = cache.update(keyable(key, symbols), value)
    def get(key: A, symbols: s.Symbols): Option[B] = cache.get(keyable(key, symbols))
    def apply(key: A, symbols: s.Symbols): B = cache(keyable(key, symbols))

    private[ExtractionCaches] def invalidate(id: Identifier): Unit =
      cache.retain(key => !(key.dependencies contains id))

    self.synchronized(caches += this)
  }

  /** A cache that relies on a [[SimpleKey]] as cache key.
    * The [[SimpleKeyable]] type class is used to generate the keys by type. */
  protected final class SimpleCache[A: SimpleKeyable, B] extends ExtractionCache[A, B]

  /** A cache that relies on a [[DependencyKey]] as cache key.
    * The [[DependencyKeyable]] type class is used to generate the keys by type. */
  protected final class DependencyCache[A <: s.Definition : DependencyKeyable, B] extends ExtractionCache[A, B]

  /** A cache that uses a custom cache key that is computed given the provided key
    * generation function. */
  protected final class CustomCache[A, B](gen: (A, s.Symbols) => CacheKey)
    extends ExtractionCache[A, B]()(new Keyable[A] {
      override def apply(key: A, symbols: s.Symbols): CacheKey = gen(key, symbols)
    })

  override def invalidate(id: Identifier): Unit = {
    for (cache <- caches) cache.invalidate(id)
  }
}
