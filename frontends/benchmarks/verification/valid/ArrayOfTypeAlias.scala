object ArrayOfTypeAlias {
  type AliasedLong = Long

  case class SomeClass(arr: Array[AliasedLong])
}