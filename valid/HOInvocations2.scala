import leon.lang._

object HOInvocations2 {
  def switch(x: Int, f: (Int) => Int, g: (Int) => Int) = if(x > 0) f else g

  def passing_1(f: (Int) => Int) = {
    switch(10, (x: Int) => x + 1, f)(2)
  } ensuring { res => res > 0 }

  def passing_2(x: Int, f: (Int) => Int, g: (Int) => Int) = {
    require(x > 0 && forall((a: Int) => a > 0 ==> f(a) > 0))
    switch(1, switch(x, f, g), g)(1)
  } ensuring { res => res > 0 }

}

// vim: set ts=4 sw=4 et:
