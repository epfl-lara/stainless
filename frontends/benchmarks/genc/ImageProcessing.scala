/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.annotation._
import stainless.lang._

import stainless.io.{
  FileInputStream => FIS,
  FileOutputStream => FOS,
  _
}
import stainless.util.{ TimePoint }

import scala.annotation.tailrec

/**
 * Some basic image processing.
 *
 * General NOTEs
 * -------------
 *
 *  Byte ranges from -128 to 127, not 0 to 255. It is important to remember
 *  that when manipulating individual component as Byte.
 *
 *  The BMP format uses little endian.
 *
 *  See https://msdn.microsoft.com/en-us/library/dd183391(v=vs.85).aspx
 *  for the full documentation.
 */
object ImageProcessing {

  /**********************************************************************
   *                                                      Constants     *
   **********************************************************************/

  // Sizes in bytes of several Windows numerical types
  @inline @cCode.inline
  val WordSize  = 2 // 16 bits, unsigned
  @inline @cCode.inline
  val DwordSize = 4 // 32 bits, unsigned
  @inline @cCode.inline
  val LongSize  = 4 // 32 bits, signed

  // Maximum size of images
  @inline @cCode.inline
  val MaxSize        = 512
  @inline @cCode.inline
  val MaxSurfaceSize = 512 * 512 // handwritten here to inline the values


  /**********************************************************************
   *                                               Basic Algorithms     *
   **********************************************************************/

  def inRange(x: Int, min: Int, max: Int): Boolean = {
    require(min <= max)
    min <= x && x <= max
  }

  def min(x: Int, y: Int): Int = {
    if (x <= y) x else y
  } ensuring { res =>
    res <= x && res <= y && (res == x || res == y)
  }

  def max(x: Int, y: Int): Int = {
    if (x <  y) y else x
  } ensuring { res =>
    x <= res && y <= res && (res == x || res == y)
  }

  def clamp(x: Int, down: Int, up: Int): Int = {
    require(down <= up)
    max(down, min(x, up))
  } ensuring { res => inRange(res, down, up) }


  /**********************************************************************
   *                                                         Status     *
   **********************************************************************/

  sealed abstract class Status {
    def isSuccess: Boolean = this.isInstanceOf[Success]
  }

  case class Success()                  extends Status
  case class OpenError()                extends Status
  case class ReadError()                extends Status
  case class DomainError()              extends Status
  case class InvalidFileHeaderError()   extends Status
  case class InvalidBitmapHeaderError() extends Status
  case class CorruptedDataError()       extends Status
  case class ImageTooBigError()         extends Status
  case class WriteError()               extends Status
  case class NotImplementedError()      extends Status

  def statusCode(s: Status)(implicit @ghost state: State): Int = s match {
    case Success()                  => StdOut.println("success");                          0
    case OpenError()                => StdOut.println("couldn't open file");               1
    case ReadError()                => StdOut.println("couldn't read some expected data"); 2
    case DomainError()              => StdOut.println("integer out of range");             3
    case InvalidFileHeaderError()   => StdOut.println("file format unsupported");          4
    case InvalidBitmapHeaderError() => StdOut.println("bitmap format unsupported");        5
    case CorruptedDataError()       => StdOut.println("the file appears to be corrupted"); 6
    case ImageTooBigError()         => StdOut.println("the image is too big");             7
    case WriteError()               => StdOut.println("couldn't write image");             8
    case NotImplementedError()      => StdOut.println("not yet implemented");              99
  }


  /**********************************************************************
   *                                                    MaybeResult     *
   **********************************************************************/

  // Basically, MaybeResult[A] is Either[A, B] where B is Status
  sealed abstract class MaybeResult[A] {
    def isDefined = this match {
      case Result(_) => true
      case _         => false
    }

    def getResult: A = {
      require(isDefined)
      this.asInstanceOf[Result[A]].result
    }

    def getStatus: Status = {
      require(!isDefined)
      this.asInstanceOf[Failure[A]].status
    }

    def toStatus: Status = {
      if (isDefined) Success()
      else           getStatus
    }
  }

  case class Result[A](result: A) extends MaybeResult[A]
  case class Failure[A](status: Status) extends MaybeResult[A] {
    require(status != Success())
  }

  // Extra operations for MaybeResult[Int].
  implicit class MaybeResultIntOps(val result: MaybeResult[Int]) {
    def expect(value: Int): MaybeResult[Int] = result match {
      case Result(res) if res == value => result
      case Result(_)                   => Failure[Int](DomainError())
      case _                           => result // a Failure remains a Failure
    }
  }

  // Combine two, three or four MaybeResult to a MaybeResult of tuple.
  def combine[A, B](a: MaybeResult[A], b: MaybeResult[B]): MaybeResult[(A, B)] = {
    if (a.isDefined) {
      if (b.isDefined) {
        Result((a.getResult, b.getResult))
      } else Failure[(A, B)](b.getStatus)
    } else Failure[(A, B)](a.getStatus)
  }

  def combine[A, B, C](a: MaybeResult[A], b: MaybeResult[B],
                       c: MaybeResult[C]): MaybeResult[(A, B, C)] = {
    val tmp = combine(combine(a, b), c)
    tmp match {
      case Result(((a, b), c)) => Result((a, b, c))
      case Failure(status)     => Failure[(A, B, C)](status)
    }
  }

  def combine[A, B, C, D](a: MaybeResult[A], b: MaybeResult[B],
                          c: MaybeResult[C], d: MaybeResult[D]): MaybeResult[(A, B, C, D)] = {
    val tmp = combine(combine(a, b, c), d)
    tmp match {
      case Result(((a, b, c), d)) => Result((a, b, c, d))
      case Failure(status)        => Failure[(A, B, C, D)](status)
    }
  }

  // Convert an Option to a MaybeResult
  def maybe[A](opt: Option[A], failStatus: Status): MaybeResult[A] = {
    require(failStatus != Success())
    opt match {
      case Some(result) => Result(result)
      case None()       => Failure(failStatus)
    }
  }

  // Special DSL for Option.
  implicit class OptionOps[A](val opt: Option[A]) {
    def toResultOr(failStatus: Status) = {
      require(failStatus != Success())
      maybe(opt, failStatus)
    }
  }


  /**********************************************************************
   *                                                Data Structures     *
   **********************************************************************/

  /*
   * Hold (some) information about the general file structure;
   * The file header is 14 bytes, the offset refers to the beginning of the file header.
   */
  case class FileHeader(size: Int, offset: Int) {
    require((14 + 40) <= size && inRange(offset, 14 + 40, size))
    // offset cannot be before the end of BitmapHeader.
  }

  /*
   * Hold basic information about the bitmap.
   *
   * See https://msdn.microsoft.com/en-us/library/dd183376(v=vs.85).aspx
   *
   * NOTE We assume that
   *  - The number of bits-per-pixel is 24 (RGB format, 8-bit channels);
   *  - No compression is used;
   *  - The palette is empty.
   */
  case class BitmapHeader(width: Int, height: Int) {
    require(0 <= width && 0 <= height)
  }

  /*
   * Represent an Image, using the usual RGB channels.
   *
   * NOTE use createImage to create a new instance of this class easily.
   */
  case class Image(r: Array[Byte], g: Array[Byte], b: Array[Byte], w: Int, h: Int) {
    require(
      r.length == MaxSurfaceSize &&
      g.length == MaxSurfaceSize &&
      b.length == MaxSurfaceSize &&
      inRange(w, 0, MaxSize) &&
      inRange(h, 0, MaxSize) &&
      inRange(w * h, 0, MaxSurfaceSize)
    )
  }

  @inline @cCode.inline // <- in order to "return" the image
  def createImage(width: Int, height: Int) = {
    require(
      inRange(width,  0, MaxSize) &&
      inRange(height, 0, MaxSize) &&
      inRange(width * height, 0, MaxSurfaceSize)
    )
    Image(
      Array.fill[Byte](MaxSurfaceSize)(0),
      Array.fill[Byte](MaxSurfaceSize)(0),
      Array.fill[Byte](MaxSurfaceSize)(0),
      width, height
    )
  }


  /**********************************************************************
   *         I/O functions for WORD, DWORD, LONG, and other helpers     *
   **********************************************************************/

  // Skip a given number of bytes, returning true on success.
  def skipBytes(fis: FIS, count: Int)(implicit state: stainless.io.State): Boolean = {
    require(fis.isOpen && 0 <= count)

    var i = 0
    var success = true

    (while (success && i < count) {
      val opt = fis.tryReadByte()
      success = opt.isDefined
      i += 1
    }) invariant (inRange(i, 0, count))

    success
  }

  // Fill the output with copies of the given byte.
  @tailrec // <- a good indicator that the C compiler could optimise out the recursion.
  def writeBytes(fos: FOS, byte: Byte, count: Int): Boolean = {
    require(fos.isOpen && 0 <= count)

    if (count == 0) true
    else fos.write(byte) && writeBytes(fos, byte, count - 1)
  }

  // Attempt to read a WORD (16-bit unsigned integer).
  // The result is represented using an Int.
  def maybeReadWord(fis: FIS)(implicit state: stainless.io.State): MaybeResult[Int] = {
    require(fis.isOpen)

    // From little to big endian
    val byte2 = fis.tryReadByte()
    val byte1 = fis.tryReadByte()

    if (byte1.isDefined && byte2.isDefined) Result(constructWord(byte1.get, byte2.get))
    else Failure[Int](ReadError())
  } ensuring { res =>
    res match {
      case Result(word) => inRange(word, 0, 65535)
      case _            => true
    }
  }

  private def constructWord(byte1: Byte, byte2: Byte): Int = {
    // Shift range appropriately to respect unsigned numbers representation
    val signed   = (byte1 << 8) | (byte2 & 0xff) // has Int type
    val unsigned = if (signed < 0) signed + (2 * 32768) else signed

    unsigned
  } ensuring { word => inRange(word, 0, 65535) }

  // Write a WORD
  def writeWord(fos: FOS, word: Int): Boolean = {
    require(fos.isOpen && inRange(word, 0, 65535))

    val (b1, b2) = destructWord(word)

    // From big endian to little endian
    fos.write(b2) && fos.write(b1)
  }

  private def destructWord(word: Int): (Byte, Byte) = {
    require(inRange(word, 0, 65535))

    // Shift range appropriately to respect integer representation
    val signed = if (word >= 32768) word - (2 * 32768) else word

    val b1 = (signed >>> 8).toByte
    val b2 = signed.toByte

    (b1, b2)
  }

  private def lemmaWord(byte1: Byte, byte2: Byte): Boolean = {
    val word = constructWord(byte1, byte2)
    val (b1, b2) = destructWord(word)
    b1 == byte1 && b2 == byte2
  }.holds

  // Attempt to read a DWORD (32-bit unsigned integer).
  // The result is represented using an Int, and values bigger than 2^31 - 1 results in DomainError.
  def maybeReadDword(fis: FIS)(implicit state: stainless.io.State): MaybeResult[Int] = {
    require(fis.isOpen)

    // From little to big endian
    def buildInt(b1: Byte, b2: Byte, b3: Byte, b4: Byte): Int = {
      require(0 <= b4)
      (b4 << 24) | ((b3 & 0xff) << 16) | ((b2 & 0xff) << 8) | (b1 & 0xff)
    } ensuring { int =>
      inRange(int, 0, 2147483647)
    }

    val byte1 = fis.tryReadByte()
    val byte2 = fis.tryReadByte()
    val byte3 = fis.tryReadByte()
    val byte4 = fis.tryReadByte() // the most significant byte

    if (byte1.isDefined && byte2.isDefined && byte3.isDefined && byte4.isDefined) {
      if (byte4.get >= 0) {
        val dword = buildInt(byte1.get, byte2.get, byte3.get, byte4.get)
        Result(dword)
      } else Failure[Int](DomainError())
    } else Failure[Int](ReadError())
  } ensuring { res =>
    res match {
      case Result(dword) => inRange(dword, 0, 2147483647)
      case _ => true
    }
  }

  // Write a DWORD
  def writeDword(fos: FOS, dword: Int): Boolean = {
    require(fos.isOpen && inRange(dword, 0, 2147483647))

    val b4 = (dword >>> 24).toByte
    val b3 = (dword >>> 16).toByte
    val b2 = (dword >>> 8).toByte
    val b1 = dword.toByte

    // Big endian to little endian conversion
    fos.write(b1) && fos.write(b2) && fos.write(b3) && fos.write(b4)
  }

  // Attempt to read a LONG (32-bit signed integer).
  // The result is represented using an Int.
  def maybeReadLong(fis: FIS)(implicit state: stainless.io.State): MaybeResult[Int] = {
    require(fis.isOpen)

    // From little to big endian
    def buildInt(b1: Byte, b2: Byte, b3: Byte, b4: Byte): Int = {
      (b4 << 24) | ((b3 & 0xff) << 16) | ((b2 & 0xff) << 8) | (b1 & 0xff)
    }

    val byte1 = fis.tryReadByte()
    val byte2 = fis.tryReadByte()
    val byte3 = fis.tryReadByte()
    val byte4 = fis.tryReadByte() // the most significant byte

    if (byte1.isDefined && byte2.isDefined && byte3.isDefined && byte4.isDefined) {
      val long = buildInt(byte1.get, byte2.get, byte3.get, byte4.get)
      Result(long)
    } else Failure[Int](ReadError())
  }

  // Write a LONG
  def writeLong(fos: FOS, long: Int): Boolean = {
    require(fos.isOpen)

    val b4 = (long >>> 24).toByte
    val b3 = (long >>> 16).toByte
    val b2 = (long >>> 8).toByte
    val b1 = long.toByte

    // Big endian to little endian conversion
    fos.write(b1) && fos.write(b2) && fos.write(b3) && fos.write(b4)
  }


  /**********************************************************************
   *                               I/O functions for the BMP format     *
   **********************************************************************/

  // Attempt to read the file header.
  // Upon success, 14 bytes have been read.
  def maybeReadFileHeader(fis: FIS)(implicit state: stainless.io.State): MaybeResult[FileHeader] = {
    require(fis.isOpen)

    var skipSuccess = skipBytes(fis, WordSize)
    val sizeRes     = maybeReadDword(fis)
    skipSuccess     = skipSuccess && skipBytes(fis, WordSize * 2)
    val offsetRes   = maybeReadDword(fis)

    combine(sizeRes, offsetRes) match {
      case _ if !skipSuccess      => Failure[FileHeader](ReadError())
      case Failure(status)        => Failure[FileHeader](status)
      case Result((size, offset)) => {
        if (14 <= size && 14 + 40 <= offset && offset <= size) Result(FileHeader(size, offset))
        else Failure[FileHeader](InvalidFileHeaderError())
      }
    }
  }

  // Attempt to read the bitmap header (minimal version).
  // Upon success, 18 bytes have been read.
  def maybeReadBitmapHeader(fis: FIS)(implicit state: stainless.io.State): MaybeResult[BitmapHeader] = {
    require(fis.isOpen)

    var skipSuccess    = skipBytes(fis, DwordSize)
    val widthRes       = maybeReadLong(fis)
    val heightRes      = maybeReadLong(fis)
    skipSuccess        = skipSuccess && skipBytes(fis, WordSize)
    val bppRes         = maybeReadWord(fis)
    val compressionRes = maybeReadWord(fis)

    combine(widthRes, heightRes, bppRes, compressionRes) match {
      case _ if !skipSuccess                => Failure[BitmapHeader](ReadError())
      case Failure(status)                  => Failure[BitmapHeader](status)
      case Result((w, h, bpp, compression)) =>
        if (w < 0 || h < 0 || bpp != 24 || compression != 0) {
          log("width", w)
          log("height", h)
          log("bpp", bpp)
          log("compression", compression)
          Failure(InvalidBitmapHeaderError())
        } else Result(BitmapHeader(w, h))
    }
  }

  def loadImageData(fis: FIS, image: Image)(implicit state: stainless.io.State): Status = {
    require(fis.isOpen)

    val size = image.w * image.h
    var i = 0
    var status: Status = Success()

    (while (status.isSuccess && i < size) {
      val rOpt = fis.tryReadByte()
      val gOpt = fis.tryReadByte()
      val bOpt = fis.tryReadByte()

      if (rOpt.isEmpty || gOpt.isEmpty || bOpt.isEmpty) {
        status = ReadError()
        log("stopped reading data abruptly after", i)
      } else {
        image.r(i) = rOpt.get
        image.g(i) = gOpt.get
        image.b(i) = bOpt.get
      }

      i += 1
    }) invariant (
      inRange(size, 0, MaxSurfaceSize) &&
      inRange(i, 0, size)
    )

    status
  }

  def saveImage(fos: FOS, image: Image): Status = {
    require(fos.isOpen)

    def writeFileHeader(): Boolean = {
      // Size: the headers and 3 channels per pixel, 1 byte per pixel component.
      val size      = 14 + 40 + image.w * image.h * 3
      val reserved  = 0 // two WORDs are reserved
      val offset    = 14 + 40 // after the two headers

      fos.write(0x42.toByte) && fos.write(0x4d.toByte) && // the signature "BM"
      writeDword(fos, size) &&
      writeWord(fos, reserved) && writeWord(fos, reserved) &&
      writeDword(fos, offset)
    }

    def writeBitmapHeader(): Boolean = {
      val size   = 40
      val w      = image.w
      val h      = image.h
      val planes = 1
      val bpp    = 24
      val comp   = 0

      writeDword(fos, size) &&
      writeLong(fos, w) && writeLong(fos, h) &&
      writeWord(fos, planes) &&
      writeWord(fos, bpp) &&
      writeWord(fos, comp) &&
      writeBytes(fos, 0, 22) // the last 22 bytes are all not relevant for us and are set to 0
    }

    def writeImage(): Boolean = {
      val count = image.w * image.h
      var i = 0
      var success = true

      (while (success && i < count) {
        success = fos.write(image.r(i)) && fos.write(image.g(i)) && fos.write(image.b(i))
        i += 1
      }) invariant (inRange(count, 0, MaxSurfaceSize) && inRange(i, 0, count))

      success
    }

    if (writeFileHeader() && writeBitmapHeader() && writeImage()) Success()
    else WriteError()
  }


  /**********************************************************************
   *                                             Logging Facilities     *
   **********************************************************************/

  def log(msg: String, x: Int)(implicit @ghost state: State): Unit = {
    StdOut.print(msg)
    StdOut.print(": ")
    StdOut.println(x)
  }

  def log(h: FileHeader)(implicit @ghost state: State): Unit = {
    log("size", h.size)
    log("offset", h.offset)
  }

  def log(h: BitmapHeader)(implicit @ghost state: State): Unit = {
    log("width", h.width)
    log("height", h.height)
  }

  /**********************************************************************
   *                            Kernel & Image Processing Algorithm     *
   **********************************************************************/

  case class Kernel(size: Int, scale: Int, kernel: Array[Int]) {
    require(
      inRange(size, 0, MaxSize) &&
      size % 2 == 1 &&
      size * size == kernel.length &&
      scale != 0 && scale != -1 // avoid division by zero and some particular overflow (*)
    )

    // (*) -2^31 / -1

    /*
     * Apply the kernel on the given channel. Return the new value for pixel component
     * at the given index.
     */
    private def apply(channel: Array[Byte], width: Int, height: Int, index: Int): Byte = {
      require(
        channel.length == MaxSurfaceSize &&
        inRange(index, 0, channel.length) &&
        inRange(width, 1, MaxSize) &&
        inRange(height, 1, MaxSize) &&
        inRange(width * height, 0, MaxSurfaceSize)
      )

      // Clamping helper
      def fix(x: Int, side: Int): Int = {
        require(0 < side)
        clamp(x, 0, side - 1)
      }

      // Get the color component at the given position in the range [0, 255]
      def at(col: Int, row: Int): Int = {
        val c = fix(col, width)
        val r = fix(row, height)

        val component = channel(r * width + c) // unsigned
        if (component < 0) component + 255.toByte else component.toInt
      } ensuring { inRange(_, 0, 255) }

      val mid = size / 2

      val i = index % width
      val j = index / width

      var res = 0
      var p   = -mid

      (while (p <= mid) {
        var q = -mid

        val oldP = p // Fix p for the inner loop (the invariant is not automatically inferred)
        (while (q <= mid) {
          val kcol = p + mid
          val krow = q + mid

          assert(inRange(krow, 0, size - 1))
          assert(inRange(kcol, 0, size - 1))

          val kidx = krow * size + kcol

          // Here, the += and * operation could overflow
          res += at(i + p, j + q) * kernel(kidx)

          q += 1
        }) invariant (oldP == p && inRange(q, -mid, mid + 1))

        p += 1
      }) invariant (inRange(p, -mid, mid + 1))

      res = clamp(res / scale, 0, 255)
      res.toByte
    }

    def apply(src: Image, dest: Image): Unit = {
      require(src.w == dest.w && src.h == dest.h)

      val size = src.w * src.h
      var i = 0

      (while (i < size) {
        dest.r(i) = apply(src.r, src.w, src.h, i)
        dest.g(i) = apply(src.g, src.w, src.h, i)
        dest.b(i) = apply(src.b, src.w, src.h, i)

        i += 1
      }) invariant (inRange(i, 0, size))
    }
  }


  /**********************************************************************
   *                                                   Main Program     *
   **********************************************************************/

  def printBool(b: Boolean)(implicit @ghost state: State): Unit = {
    if (b) StdOut.println("true")
    else StdOut.println("false")
  }

  @cCode.`export`
  def main(): Int = {
    implicit val state = stainless.io.newState
    val input  = FIS.open("input.bmp")
    val output = FOS.open("output.bmp")

    val status =
      if (input.isOpen && output.isOpen) process(input, output)
      else OpenError()

    output.close()
    input.close()

    statusCode(status)
  }

  def process(fis: FIS, fos: FOS)(implicit state: stainless.io.State): Status = {
    require(fis.isOpen && fos.isOpen)

    /*
     * // Smooth kernel
     * val kernel = Kernel(3, 1, Array(1, 1, 1, 1, 2, 1, 1, 1, 1))
     */

    /* // Edges
     * val kernel = Kernel(5, 1, Array(
     *   0,  0, -1,  0,  0,
     *   0,  0, -1,  0,  0,
     *  -1, -1,  8, -1, -1,
     *   0,  0, -1,  0,  0,
     *   0,  0, -1,  0,  0
     * ))
     */

    /* // Identity
     * val kernel = Kernel(5, 1, Array(
     *   0,  0,  0,  0,  0,
     *   0,  0,  0,  0,  0,
     *   0,  0,  1,  0,  0,
     *   0,  0,  0,  0,  0,
     *   0,  0,  0,  0,  0
     * ))
     */

    /* // Sharpen
     * val kernel = Kernel(5, 8, Array(
     *   -1, -1, -1, -1, -1,
     *   -1,  2,  2,  2, -1,
     *   -1,  2,  8,  2, -1,
     *   -1,  2,  2,  2, -1,
     *   -1, -1, -1, -1, -1
     * ))
     */

    // Blur
    val kernel = Kernel(5, 25, Array(
      1, 1, 1, 1, 1,
      1, 1, 1, 1, 1,
      1, 1, 1, 1, 1,
      1, 1, 1, 1, 1,
      1, 1, 1, 1, 1
    ))

    def processImage(src: Image): Status = {
      // Compute the processing time, without I/Os
      val t1 = TimePoint.now()

      val dest = createImage(src.w, src.h)
      kernel.apply(src, dest)

      val t2 = TimePoint.now()
      val ms = TimePoint.elapsedMillis(t1, t2)
      StdOut.print("Computation time: ")
      StdOut.print(ms)
      StdOut.println("ms.")

      saveImage(fos, dest)
    }

    val fileHeaderRes   = maybeReadFileHeader(fis)
    val bitmapHeaderRes = maybeReadBitmapHeader(fis)

    val status = combine(fileHeaderRes, bitmapHeaderRes) match {
      case Failure(status) =>
        status

      /*
       * Report an error when the file is corrupted, i.e. it's too small.
       * 40 is the minimal bitmap header size, 14 is the file header size.
       * Note that more sanity check could be done but that's not the main
       * point of this example.
       */
      case Result((fh, bh)) if fh.size <= 14 + 40 =>
        CorruptedDataError()

      case Result((fh, bh)) =>
        log(fh)
        log(bh)

        // Skip bytes until the start of the bitmap data
        val toSkip  = fh.offset - (14 + 18) // some bytes were already eaten
        val success = skipBytes(fis, toSkip)

        // Break test of size so we avoid overflows.
        if (!success)                                       CorruptedDataError()
        else if (bh.width > MaxSize || bh.height > MaxSize) ImageTooBigError()
        else if (bh.width * bh.height > MaxSurfaceSize)     ImageTooBigError()
        else {
          val image  = createImage(bh.width, bh.height)
          val status = loadImageData(fis, image)
          if (status.isSuccess) processImage(image)
          else                  status
        }
    }

    status
  }

}

