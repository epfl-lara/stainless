import stainless.lang._

object FunctionMaps {

  type Env[K, V] = K => Option[V]

  def defined[K, V](env: Env[K, V], k: K): Boolean =
    env(k).isDefined

  def merge[K, V](env1: Env[K, V], env2: Env[K, V]): Env[K, V] = {
    (k: K) => env1(k).orElse(env2(k))
  }

  def empty[K, V]: Env[K, V] = { (k: K) => None() }

  def update[K, V](env: Env[K, V], k: K, v: V): Env[K, V] = {
    (k1: K) => if (k1 == k) Some(v) else env(k1)
  }

  def single[K, V](k: K, v: V): Env[K, V] = update(empty[K, V], k, v)

  def leftIden[K, V](env: Env[K, V], k0: K): Boolean = {
    merge[K, V](empty[K, V], env)(k0) == env(k0)
  }.holds

  def rightIden[K, V](env: Env[K, V], k0: K): Boolean = {
    merge[K, V](env, empty[K, V])(k0) == env(k0)
  }.holds

  def assoc[K, V](env1: Env[K, V], env2: Env[K, V], env3: Env[K, V], k0: K): Boolean = {
    merge[K, V](merge[K, V](env1, env2), env3)(k0) ==
    merge[K, V](env1, merge[K, V](env2, env3))(k0)
  }.holds
}
