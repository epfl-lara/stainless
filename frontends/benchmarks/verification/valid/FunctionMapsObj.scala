import stainless.lang._
import stainless.annotation._

object FunctionMapsObj {

  case class Env[K, V](f: K => Option[V]) { self =>
    def apply(k: K): Option[V] = f(k)

    def isDefined(k: K): Boolean = apply(k).isDefined

    def update(k: K, v: V): Env[K, V] = {
      Env((k1: K) => if (k1 == k) Some(v) else apply(k1))
    }

    def merge(that: Env[K, V]): Env[K, V] =
      Env((k: K) => self(k).orElse(that(k)))
  }

  object Env {
    def empty[K, V]: Env[K, V] = Env((k: K) => None())

    def single[K, V](k: K, v: V): Env[K, V] =
      Env.empty[K, V].update(k, v)

    def leftIden[K, V](env: Env[K, V], k0: K): Boolean = {
      Env.empty[K, V].merge(env)(k0) == env(k0)
    }.holds

    def rightIden[K, V](env: Env[K, V], k0: K): Boolean = {
      env.merge(Env.empty[K, V])(k0) == env(k0)
    }.holds

    def assoc[K, V](env1: Env[K, V], env2: Env[K, V], env3: Env[K, V], k0: K): Boolean = {
      env1.merge(env2).merge(env3)(k0) ==
      env1.merge(env2.merge(env3))(k0)
    }.holds
  }
}
