import stainless.*
import stainless.annotation.*
import stainless.collection.*
import stainless.lang.*
import stainless.lang.{None, Option, Some}
import stainless.lang.StaticChecks.*
import stainless.proof.*

object i839a:

  case class A() {}

  case class B(a: A = new A)

  case class C():
    val b = new B

  def test(): Unit =
    assert(C().b == B(A()))
