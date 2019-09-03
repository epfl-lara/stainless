import stainless.lang._
import stainless.collection._

object BVMaxInterpret {

  case class Reg(n: BigInt)

  sealed abstract class Op {
    def out: Reg
  }
  case class BVSge(out: Reg, ra: Reg, rb: Reg) extends Op
  case class BVNeg(out: Reg, ra: Reg)          extends Op
  case class BVXor(out: Reg, ra: Reg, rb: Reg) extends Op
  case class BVAnd(out: Reg, ra: Reg, rb: Reg) extends Op

  case class State(
    registers: CMap[Reg, Int],
  ) {
    def load(reg: Reg): Int = registers(reg)
    def store(reg: Reg, v: Int): State = copy(registers = registers.updated(reg, v))
  }

  object State {
    def empty: State = State(CMap(_ => 0))
  }

  def eval1(op: Op, state: State): Int = op match {
    case BVSge(_, ra, rb) =>
      if (state.load(ra) >= state.load(rb)) 1 else 0

    case BVNeg(_, ra) =>
      -state.load(ra)

    case BVXor(_, ra, rb) =>
      state.load(ra) ^ state.load(rb)

    case BVAnd(_, ra, rb) =>
      state.load(ra) & state.load(rb)
  }

  def eval(op: Op, state: State): State = {
    val res = eval1(op, state)
    state.store(op.out, res)
  }

  case class Program(stmts: List[Op], ret: Reg)

  def interpret(prog: Program, init: State): Int = {
    def go(stmts: List[Op], state: State): State = {
      decreases(stmts)
      stmts match {
        case Nil() => state
        case Cons(op, rest) => go(rest, eval(op, state))
      }
    }

    val end = go(prog.stmts, init)
    end.load(prog.ret)
  }

  val r0 = Reg(0)
  val r1 = Reg(1)
  val r2 = Reg(2)
  val r3 = Reg(3)
  val r4 = Reg(4)
  val r5 = Reg(5)
  val r6 = Reg(6)

  def bvmax(r0v: Int, r1v: Int) = {
    val init = State.empty.store(r0, r0v).store(r1, r1v)

    val prog = Program(
      List(
        BVSge(r2, r0, r1),
        BVNeg(r3, r2),
        BVXor(r4, r0, r1),
        BVAnd(r5, r3, r4),
        BVXor(r6, r1, r5),
      ),
      r6
    )

    interpret(prog, init)
  }

  def thm(a: Int, b: Int) = {
    assert(bvmax(a, b) == stainless.math.max(a, b))
  }

}
