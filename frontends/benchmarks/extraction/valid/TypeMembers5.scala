import stainless.lang._

object TypeMembers5 {

  type Env = String => Option[Int]

  def update(env: Env, s: String, v: Int): Env = {
    (s1: String) => if (s1 == s) Some(v) else env(s1)
  }
}

