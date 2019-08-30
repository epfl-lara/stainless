
object GhostDafny {

  import stainless.annotation._

  sealed abstract class GhostDt
  object GhostDt {
    case class Nil(@ghost extraInfo: BigInt) extends GhostDt
    case class Cons(data: BigInt, tail: GhostDt, @ghost moreInfo: BigInt) extends GhostDt
  }

  object GhostTests {

    def M(dt: GhostDt): BigInt = {
      @ghost var g: BigInt = 5

      var r: BigInt = 0

      r = g;         // error: RHS is ghost, LHS is not
      r = F(18, g);  // error: RHS is a ghost and will not be available at run time
      r = G(20, g);  // it's fine to pass a ghost as a parameter to a non-ghost, because
      // only the ghost goes away during compilation
      r = N(22, g);  // ditto
      r = N(g, 22);  // error: passing in 'g' as non-ghost parameter
      r = P(24, 22); // error: 'P' is ghost, but its result is assigned to a non-ghost

      dt match {
        case GhostDt.Nil(gg) => ()
        case GhostDt.Cons(dd, tt, gg) =>
          r = G(dd, dd);  // fine
          r = G(dd, gg);  // fine
          r = G(gg, gg);  // error: cannot pass ghost 'gg' as non-ghost parameter to 'G'
      }

      var dd: GhostDt = GhostDt.Nil(0);
      dd = GhostDt.Nil(g);  // fine
      dd = GhostDt.Cons(g, dt, 2);  // error: cannot pass 'g' as non-ghost parameter
      @ghost var dtg = GhostDt.Cons(g, dt, 2);  // fine, since result is ghost

      r
    }

    @ghost
    def F(x: BigInt, y: BigInt): BigInt = {
      y
    }

    def G(x: BigInt, @ghost y: BigInt): BigInt = {
      y // error: cannot return a ghost from a non-ghost function
    }

    def H(dt: GhostDt): BigInt = {
      dt match {
        case GhostDt.Nil(gg) => gg  // error: cannot return a ghost from a non-ghost function
        case GhostDt.Cons(dd, tt, gg) =>  dd + gg  // error: ditto
      }
    }

    def N(x: BigInt, @ghost y: BigInt): BigInt = {
      x
    }

    @ghost
    def P(x: BigInt, y: BigInt): BigInt = {
      @ghost var r: BigInt = 0;
      @ghost var g: BigInt = 5;
      r = y;  // allowed, since the entire method is ghost
      r = r + g;  // fine, for the same reason
      r = N(20, 20);  //fine: call to non-ghost method from ghost method is okay because purity
      r
    }

  }
}
