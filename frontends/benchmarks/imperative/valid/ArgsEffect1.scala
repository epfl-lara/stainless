import stainless.annotation._

object ArgsEffect1 {

  case class BitStream(bits: Array[Byte]) {
    @pure
    def validate_offset_bits(i: Int): Boolean = true
  }

  @mutable
  trait Codec {
    def bitStream: BitStream

    def peekBit(): Unit = {
      val isValidPrecondition = bitStream.validate_offset_bits(1)
    }
  }
}