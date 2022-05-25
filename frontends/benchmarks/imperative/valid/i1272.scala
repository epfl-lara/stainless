import stainless.io._

object i1272 {
  def read(fis: FileInputStream)(implicit s: State): Unit = {
    require(fis.isOpen)
    val a1 = fis.tryReadByte()
    val a2 = fis.tryReadByte()
  }

  def write(fos: FileOutputStream): Unit = {
    require(fos.isOpen)
    fos.write(1)
    fos.write(2)
  }
}