import stainless.annotation.ghost

object ErasedDafny {

  sealed abstract class ErasedDt
  object ErasedDt {
    case class Nil(erased extraInfo: BigInt) extends ErasedDt
    case class Cons(data: BigInt, tail: ErasedDt, erased moreInfo: BigInt) extends ErasedDt
  }

  object ErasedTests {

    def M(dt: ErasedDt): BigInt = {
      erased var g: BigInt = 5

      var r: BigInt = 0

      r = g;         // error: RHS is erased, LHS is not
      r = F(18, g);  // error: RHS is erased and will not be available at run time
      r = G(20, g);  // it's fine to pass an erased value as a parameter to a non-erased method, because
      // only the erased part goes away during compilation
      r = N(22, g);  // ditto
      r = N(g, 22);  // error: passing in 'g' as non-erased parameter
      r = P(24, 22); // error: 'P' is erased, but its result is assigned to a non-erased variable

      dt match {
        case ErasedDt.Nil(gg) => ()
        case ErasedDt.Cons(dd, tt, gg) =>
          r = G(dd, dd);  // fine
          r = G(dd, gg);  // fine
          r = G(gg, gg);  // error: cannot pass erased 'gg' as non-erased parameter to 'G'
      }

      var dd: ErasedDt = ErasedDt.Nil(0);
      dd = ErasedDt.Nil(g);  // fine
      dd = ErasedDt.Cons(g, dt, 2);  // error: cannot pass 'g' as non-erased parameter
      erased var dtg = ErasedDt.Cons(g, dt, 2);  // fine, since result is erased

      r
    }

    @ghost def F(x: BigInt, y: BigInt): BigInt = {
      y
    }

    def G(x: BigInt, erased y: BigInt): BigInt = {
      y // error: cannot return an erased value from a non-erased function
    }

    def H(dt: ErasedDt): BigInt = {
      dt match {
        case ErasedDt.Nil(gg) => gg  // error: cannot return an erased value from a non-erased function
        case ErasedDt.Cons(dd, tt, gg) =>  dd + gg  // error: ditto
      }
    }

    def N(x: BigInt, erased y: BigInt): BigInt = {
      x
    }

    @ghost def P(x: BigInt, y: BigInt): BigInt = {
      erased var r: BigInt = 0;
      erased var g: BigInt = 5;
      r = y;  // allowed, since the entire method is erased
      r = r + g;  // fine, for the same reason
      r = N(20, 20);  //fine: call to non-erased method from erased method is okay because purity
      r
    }

  }
}
