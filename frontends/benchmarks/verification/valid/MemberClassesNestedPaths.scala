import stainless.lang._
import stainless.collection._

// Fields whose type has nested path-dependent types, as `List[Stmt]` in `Block`
object MemberClassesNestedPaths {
  trait Lang {
    sealed abstract class Stmt
    case class Block(stmts: List[Stmt]) extends Stmt
    case class Opt(s: Option[Stmt]) extends Stmt
    case class Skip() extends Stmt

    final def isSkip(s: Stmt): Boolean = s match {
      case Skip() => true
      case _ => false
    }

    // The elements of `stmts` are `Lang.this.Stmt`s
    final def skips(stmts: List[Stmt]): BigInt = {
      decreases(stmts)
      stmts match {
        case Cons(s, rest) => (if (isSkip(s)) BigInt(1) else BigInt(0)) + skips(rest)
        case Nil() => BigInt(0)
      }
    }.ensuring(res => 0 <= res && res <= stmts.size)

    final def blockSkips(s: Stmt): BigInt = s match {
      case Block(stmts) => skips(stmts)
      case Opt(Some(s2)) => if (isSkip(s2)) BigInt(1) else BigInt(0)
      case _ => BigInt(0)
    }
  }

  def stmts(l: Lang): List[l.Stmt] = List(l.Skip(), l.Opt(Some(l.Skip())))

  def test(l: Lang): Unit = {
    val b = l.Block(stmts(l))
    assert(b.stmts.size == 2)
    val first: l.Stmt = b.stmts.head
    assert(l.isSkip(first))
    assert(l.skips(b.stmts) == 1)
    val o = l.Opt(Some(b))
    val inner: l.Stmt = o.s.get
    assert(l.blockSkips(inner) == 1)
  }
}
