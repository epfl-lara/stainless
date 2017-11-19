// /* From ESOP 2014, Kuwahara et al */

// FIXME: to uncomment when higher order contracts are implemented
// what should we do with this example?
// we would like to pass `down` and `up` directly to `app`

// import stainless.lang._
// import stainless.util._
// import stainless.util.Random._

object UpDown {

//   def app(f: BigInt => Unit)(x: BigInt) = f(x)

//   def down(x: BigInt): Unit = {
//     require(x >= 0)
//     if (x == 0) {
//       ()
//     } else {
//       down(x - 1)
//     }
//   }

//   def up(x: BigInt): Unit = {
//     require(x <= 0)
//     if (x == 0) {
//       ()
//     } else {
//       up(x + 1)
//     }
//   }

//   def main(implicit state: State): Unit = {
//     val t1 = Random.nextBigInt
//     val t2 = Random.nextBigInt
//     if (t1 > 0) app(down)(t1)
//     else if (t2 < 0) app(up)(t2)
//     else ()
//   }
}
