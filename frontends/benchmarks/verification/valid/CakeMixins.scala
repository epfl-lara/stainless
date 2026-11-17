import stainless.lang._

object CakeMixins {
  trait Types { self: Trees =>
    sealed abstract class Type extends Tree
    case class IntType() extends Type
    case class BoolType() extends Type
  }

  trait Exprs { self: Trees =>
    abstract class Expr extends Tree {
      def getType: Type
    }
    case class IntLit(v: BigInt) extends Expr {
      def getType: Type = IntType()
    }
    case class Eq(l: Expr, r: Expr) extends Expr {
      def getType: Type = BoolType()
    }
    final def isBool(e: Expr): Boolean = e.getType match {
      case BoolType() => true
      case _ => false
    }
  }

  trait Trees extends Types with Exprs {
    abstract class Tree
    def name: String = "trees"
  }

  // Extending the cake with new expressions
  trait ExtTrees extends Trees {
    case class Neg(e: Expr) extends Expr {
      def getType: Type = IntType()
    }
    override def name: String = "ext"
  }

  // Stackable modifications, resolved by linearization
  trait Printing extends Trees {
    override def name: String = "printing " + super.name
  }
  trait Tracing extends Trees {
    override def name: String = "tracing " + super.name
  }
  trait Fixed extends Trees {
    override def name: String = "fixed"
  }

  case object ext extends ExtTrees with Printing
  case object both extends ExtTrees with Printing with Tracing
  case object swapped extends ExtTrees with Tracing with Printing
  case object fixedFirst extends Fixed with ExtTrees
  case object fixedLast extends ExtTrees with Fixed

  def name(t: Trees): String = t.name

  def test: Unit = {
    assert(ext.isBool(ext.Eq(ext.IntLit(1), ext.Neg(ext.IntLit(2)))))
    assert(!ext.isBool(ext.Neg(ext.IntLit(2))))
    assert(ext.name == "printing ext")
    assert(name(ext) == "printing ext")
    assert(name(both) == "tracing printing ext")
    assert(name(swapped) == "printing tracing ext")
    assert(name(fixedFirst) == "ext")
    assert(name(fixedLast) == "fixed")
  }
}
