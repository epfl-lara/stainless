package crypto

import crypto.Pratt._
import crypto.Curve._
import stainless.collection.{List => SList, Cons, Nil}
import java.nio.file.{Files, Path}

/**
 * Establishes TCB T6: runs the verified Pratt checker on the four curve certificates.
 * Also: broken certificates are rejected, the constants match the oracle and
 * BigInteger.isProbablePrime, and the verified scalarMul reproduces every [k]G
 * vector, [n]G == O and [n-1]G == -G.
 */
object PrattJvm {
  private var checks = 0
  private def check(cond: Boolean, msg: => String): Unit = {
    checks += 1
    if (!cond) { System.err.println(s"FAIL: $msg"); sys.exit(1) }
  }
  private def hex(s: String) = BigInt(s, 16)
  private def toScala[A](l: SList[A]): List[A] = l match {
    case Cons(h, t) => h :: toScala(t)
    case _          => scala.Nil
  }
  private def fromScala[A](l: List[A]): SList[A] = l.foldRight(Nil[A](): SList[A])((h, t) => Cons(h, t))

  def main(args: Array[String]): Unit = {
    val dir = Path.of(args.headOption.getOrElse("verification/crypto-oracle/vectors"))
    def load(f: String) = ujson.read(Files.readString(dir.resolve(f))).arr.toSeq

    val certs = Seq(
      ("secp256k1 p", PrattCerts.secp256k1PCert, PrattCerts.secp256k1P),
      ("secp256k1 n", PrattCerts.secp256k1NCert, PrattCerts.secp256k1N),
      ("P-256 p", PrattCerts.p256PCert, PrattCerts.p256P),
      ("P-256 n", PrattCerts.p256NCert, PrattCerts.p256N))
    // T6: the verified checker accepts each certificate.
    for ((name, cert, n) <- certs) {
      check(certifies(cert, n), s"certificate of $name rejected")
      check(n.bigInteger.isProbablePrime(64), s"$name not prime by BigInteger")
      for (s <- toScala(cert)) check(s.p.bigInteger.isProbablePrime(64), s"step ${s.p} of $name")
    }
    // The constants agree with the oracle's order_mult_nG edge cases and the curve parameters.
    val edge = load("edge_cases_vectors.json")
    def order(curve: String) = hex(edge.find(v => v("curve").str == curve && v("name").str == "order_mult_nG").get("k").str)
    check(order("secp256k1") == PrattCerts.secp256k1N && order("NIST_P256") == PrattCerts.p256N, "group orders")
    check(Curves.secp256k1 == CurveJvm.curves("secp256k1")._1 && Curves.p256 == CurveJvm.curves("NIST_P256")._1, "curve parameters")

    // Broken certificates are rejected.
    for ((name, cert, n) <- certs) {
      val steps = toScala(cert)
      val last = steps.last
      def withLast(s: PrattStep) = fromScala(steps.init :+ s)
      // A wrong primitive root: a = 1 has order 1, and -1 has order 2.
      check(!certifies(withLast(last.copy(a = BigInt(1))), n), s"a = 1 accepted for $name")
      check(!certifies(withLast(last.copy(a = last.p - 1)), n), s"a = -1 accepted for $name")
      // A factor dropped (product != p - 1), a corrupted cofactor, an uncertified q (steps reordered).
      check(!certifies(withLast(last.copy(factors = fromScala(toScala(last.factors).tail))), n), s"dropped factor accepted for $name")
      val f0 = toScala(last.factors).head
      check(!certifies(withLast(last.copy(factors = Cons(f0.copy(cofactor = f0.cofactor + 1), last.factors.tail))), n), s"bad cofactor for $name")
      check(!certifies(fromScala(last :: steps.init), n), s"unordered certificate accepted for $name")
      check(!certifies(fromScala(List(last)), n), s"last step without its factor certificates accepted for $name")
      check(!certifies(withLast(last.copy(factors = Cons(PrattFactor(2, 0, (last.p - 1) / 2), last.factors))), n), s"factor 2^0 accepted for $name")
      // A certificate for a different number.
      check(!certifies(cert, n + 2), s"certificate reused for ${name} + 2")
    }
    // A composite with a Fermat witness cannot be certified: 561 = 3*11*17 (Carmichael), every a fails some cofactor.
    val f561 = fromScala(List(PrattFactor(2, 4, 280), PrattFactor(5, 1, 112), PrattFactor(7, 1, 80)))
    val small = fromScala(List(
      PrattStep(3, 2, fromScala(List(PrattFactor(2, 1, 1)))),
      PrattStep(5, 2, fromScala(List(PrattFactor(2, 2, 2)))),
      PrattStep(7, 3, fromScala(List(PrattFactor(2, 1, 3), PrattFactor(3, 1, 2))))))
    for (a <- BigInt(2) until 561)
      check(!certifies(fromScala(toScala(small) :+ PrattStep(561, a, f561)), BigInt(561)), s"561 certified with a = $a")

    // An uncertified composite q: 560 == 560^1, 2^1 != 1 and 2^560 == 1 (mod 561), so only known.contains(q) rejects it.
    check(!certifies(fromScala(List(PrattStep(561, 2, fromScala(List(PrattFactor(560, 1, 1)))))), BigInt(561)), "561 certified by the uncertified q = 560")

    // Verified scalarMul on every [k]G vector and the order edge cases.
    for (v <- load("secp256k1_vectors.json") ++ load("nist_p256_vectors.json") ++ edge if v("op").str == "mul") {
      val (c, g, _) = CurveJvm.curves(v("curve").str)
      val want = if (v("result").isNull) InfinityPoint else AffinePoint(hex(v("result")("x").str), hex(v("result")("y").str))
      check(scalarMul(hex(v("k").str), g, c) == want, s"scalarMul: $v")
    }
    for ((name, (c, g, n)) <- CurveJvm.curves) {
      check(scalarMul(n, g, c) == InfinityPoint, s"[n]G on $name")
      check(scalarMul(n - 1, g, c) == neg(g, c), s"[n-1]G == -G on $name")
    }

    println(s"Pratt/scalarMul JVM: 4 certificates (${certs.map(c => toScala(c._2).size).sum} steps), $checks checks passed")
  }
}
