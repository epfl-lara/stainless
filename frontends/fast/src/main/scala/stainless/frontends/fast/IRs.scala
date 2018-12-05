package stainless.frontends.fast


trait IRs extends inox.parser.IRs with extraction.DottyToInoxIR {

  object StainlessHoleTypes {
    case object MatchCase extends HoleType
  }
}
