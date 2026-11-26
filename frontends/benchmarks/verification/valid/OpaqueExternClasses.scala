import stainless.lang._
import stainless.annotation._

object OpaqueExternClasses {
  // A process handle: its field is opaque and mutable
  @extern
  class Proc(val p: java.lang.Process) {
    def send(x: BigInt): BigInt = {
      p.getOutputStream.write(x.toInt)
      x
    }.ensuring(res => res == x)
  }

  // A pure handle: immutable field
  @extern @pure
  case class Ctx(underlying: java.util.concurrent.atomic.AtomicLong) {
    def id: BigInt = BigInt(underlying.get).ensuring(res => res >= 0)
  }

  case class Solver(proc: Proc, ctx: Ctx, n: BigInt)

  def run(s: Solver): BigInt = {
    s.proc.send(s.n) + s.ctx.id
  }.ensuring(res => res >= s.n)

  // The methods of a pure extern class are deterministic
  def sameCtx(c: Ctx): Unit = {
    assert(c.id == c.id)
  }

  @extern
  def start(cmd: String): Proc = new Proc(Runtime.getRuntime.exec(Array(cmd)))

  def make(cmd: String, ctx: Ctx): Solver = Solver(start(cmd), ctx, 0)
}
