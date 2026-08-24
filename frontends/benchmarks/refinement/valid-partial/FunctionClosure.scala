
// fails on missing measure for termination of funWhile

// this test only checks that the parameters are in correct order in the closure
//  meaning, this:
//    def funWhile(f: ({ param0: BigInt | (from <= param0) }) => Unit, from: BigInt, i: BigInt): (Unit, BigInt)
//  would be incorrect, since `f` type depends on `from`.
def fun(from: BigInt)(f: {i: BigInt with from <= i} => Unit): Unit =
  var i: (BigInt with from <= i) = from.asInstanceOf[{i: BigInt with from <= i}]
  while i < 10 do
    f(i)
    i = (i + 1).asInstanceOf[{i: BigInt with from <= i}]