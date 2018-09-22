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

  protected abstract class SimpleKey extends CacheKey
  protected abstract class SimpleKeyable[T] extends Keyable[T] {
    override def apply(key: T, symbols: s.Symbols): SimpleKey
  }

  private final class FunctionKey private(private val fd: s.FunDef) extends SimpleKey {
    override def dependencies = Set(fd.id)

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

  protected def getSimpleKey(id: Identifier)(implicit symbols: s.Symbols): SimpleKey =
    symbols.lookupFunction(id).map(FunctionKey(_, symbols))
      .orElse(symbols.lookupSort(id).map(SortKey(_, symbols)))
      .getOrElse(throw new RuntimeException(
        "Couldn't find symbol " + id.asString + " in symbols " + symbols.asString))


  protected sealed class SeqKey(private val keys: Seq[CacheKey]) extends CacheKey {
    override val dependencies = keys.flatMap(_.dependencies).toSet

    override def hashCode: Int = keys.hashCode
    override def equals(that: Any): Boolean = that match {
      case uk: SeqKey => keys == uk.keys
      case _ => false
    }

    override def toString: String = s"SeqKey(${keys.mkString(", ")})"
  }


  protected sealed class ValueKey[T](private val value: T) extends CacheKey {
    override def dependencies = Set()

    override def hashCode: Int = value.hashCode
    override def equals(that: Any): Boolean = that match {
      case (vk: ValueKey[_]) => value == vk.value
      case _ => false
    }

    override def toString: String = s"ValueKey($value)"
  }


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

  protected final class SimpleCache[A: SimpleKeyable, B] extends ExtractionCache[A, B]

  protected final class DependencyCache[A <: s.Definition : DependencyKeyable, B] extends ExtractionCache[A, B]

  protected final class CustomCache[A, B](gen: (A, s.Symbols) => CacheKey)
    extends ExtractionCache[A, B]()(new Keyable[A] {
      override def apply(key: A, symbols: s.Symbols): CacheKey = gen(key, symbols)
    })

  override def invalidate(id: Identifier): Unit = {
    for (cache <- caches) cache.invalidate(id)
  }
}
