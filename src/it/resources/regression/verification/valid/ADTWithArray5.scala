import leon.collection._

object ADTWithArray5 {

  case class HashTable(table: Array[BigInt]) {
    require(table.length > 0)

    def apply(index: Int): BigInt = {
      require(index >= 0 && index < table.length)
      table(index)
    }
  }

}
