// import stainless.lang._

object TraitVar2 {

  sealed trait TraitWithVar {
    var prop: BigInt
    def doStuff(x: BigInt) = {
      prop = x
    }
  }

  case class ConcreteWithTraitVar(var prop: BigInt) extends TraitWithVar

  sealed trait AbstractWithVar {
    var prop2: BigInt
    def doStuff2(x2: BigInt) = {
      prop2 = x2
    }
  }

  case class ConcreteWithAbstractVar(var prop2: BigInt) extends AbstractWithVar

  case class NormalVar(var prop3: BigInt) {
    def doStuff3(x3: BigInt) = {
      prop3 = x3
    }
  }

  case class NormalClass(hello: BigInt) {
    def double = NormalClass(hello * 2)
  }

  case class NormalClassWithVal(hello: BigInt) {
    val double = hello * 2
    def quad = double + double
  }

  implicit class ImplicitClass(val underlying: BigInt) {
    def double = underlying * 2
  }

  def theorem1(t: TraitWithVar) = {
    require(t.prop == 42)
    t.doStuff(100)
    assert(t.prop == 100)
  }

  def theorem1bis(t: ConcreteWithTraitVar) = {
    require(t.prop == 42)
    t.doStuff(100)
    assert(t.prop == 100)
  }

  def theorem2(t: AbstractWithVar) = {
    require(t.prop2 == 42)
    t.doStuff2(100)
    assert(t.prop2 == 100)
  }

  def theorem2bis(t: ConcreteWithAbstractVar) = {
    require(t.prop2 == 42)
    t.doStuff2(100)
    assert(t.prop2 == 100)
  }

  def theorem3(t: NormalVar) = {
    require(t.prop3 == 42)
    t.doStuff3(100)
    assert(t.prop3 == 100)
  }

  def theorem4(x: BigInt) = {
    assert(x.double == x * 2)
  }

  def theorem5(a: NormalClass) = {
    require(a.hello == 42)
    assert(a.double.hello == BigInt(42) * 2)
  }

  def theorem5(a: NormalClassWithVal) = {
    assert(a.quad == a.hello * 4)
  }

}
