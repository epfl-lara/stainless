import stainless.io._

object i1272 {

  def writing(fos: FileOutputStream): Unit = {
    // Invalid, we need fos.isOpen
    fos.write(1)
  }
}