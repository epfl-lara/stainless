/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.wasmgen.wasm

object Types {
  trait AbsType {
    val size: Int
    def bitSize: Int = size * 8
  }
  trait Type extends AbsType
  trait TruncType extends AbsType
  case object i32 extends Type with TruncType { val size = 4 }
  case object i64 extends Type { val size = 8 }
  case object f32 extends Type { val size = 4 }
  case object f64 extends Type { val size = 8 }
  case object void extends Type {
    val size = 0
    override def toString = ""
  }

  case object i8 extends TruncType { val size = 1 }
  case object i16 extends TruncType { val size = 2 }
}
