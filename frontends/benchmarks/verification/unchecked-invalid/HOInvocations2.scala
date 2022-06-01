/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object HOInvocations2 {
  def switch(x: BigInt, f: (BigInt) => BigInt, g: (BigInt) => BigInt) = if(x > 0) f else g

  def failling_2(x: BigInt, f: (BigInt) => BigInt, g: (BigInt) => BigInt) = {
    require(x > 0 && forall((a: BigInt) => a > 0 ==> f(a) > 0))
    switch(1, switch(x, f, g), g)(0)
  } ensuring { res => res > 0 }
}

// vim: set ts=4 sw=4 et:
