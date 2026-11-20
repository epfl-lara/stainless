import stainless.lang._

// Abstract vals whose type is a member class
object MemberClassesAbstractVals {
  trait Lang {
    abstract class Expr
    case class Lit(n: BigInt) extends Expr

    abstract class Named {
      val value: Expr
    }
    case class Def(value: Expr) extends Named

    // An open subclass that inherits the abstract val
    abstract class Tagged extends Named {
      val tag: BigInt
    }
    case class TaggedDef(value: Expr, tag: BigInt) extends Tagged

    def valueOf(n: Named): Expr = n.value
  }

  def test(l: Lang): Unit = {
    val d = l.Def(l.Lit(1))
    val v: l.Expr = d.value
    val w: l.Expr = l.valueOf(d)
    assert(v.isInstanceOf[l.Lit])
    val t = l.TaggedDef(l.Lit(2), 3)
    val u: l.Expr = (t: l.Tagged).value
    assert(u.isInstanceOf[l.Lit])
  }
}
