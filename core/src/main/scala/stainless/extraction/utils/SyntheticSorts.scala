/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package utils

trait SyntheticSorts extends ExtractionCaches { self: ExtractionPipeline =>

  protected object OptionSort {
    import t._
    import t.dsl._

    private[this] val syntheticOption: t.ADTSort = {
      val Seq(option, some, none) =
        Seq("Option", "Some", "None").map(name => ast.SymbolIdentifier("stainless.lang." + name))
      val value = FreshIdentifier("value")
      mkSort(option)("A") { case Seq(aT) => Seq((some, Seq(t.ValDef(value, aT))), (none, Seq())) }
    }

    private[this] val syntheticIsEmpty: s.Symbols => t.FunDef = {
      def createFunction(option: Identifier, none: Identifier): t.FunDef = {
        val isEmpty = ast.SymbolIdentifier("stainless.lang.Option.isEmpty")
        mkFunDef(isEmpty, t.Unchecked)("A") {
          case Seq(aT) => (Seq("x" :: T(option)(aT)), t.BooleanType(), { case Seq(v) => v is none })
        }
      }

      val syntheticFunction: t.FunDef = createFunction(
        syntheticOption.id,
        syntheticOption.constructors.find(_.fields.isEmpty).get.id)

      val cache = new ExtractionCache[s.ADTSort, t.FunDef]
      (symbols: s.Symbols) => symbols.lookup.get[s.ADTSort]("stainless.lang.Option") match {
        case Some(sort) => cache.cached(sort, symbols) {
          createFunction(sort.id, sort.constructors.find(_.fields.isEmpty).get.id)
        }
        case None => syntheticFunction
      }
    }

    private[this] val syntheticGet: s.Symbols => t.FunDef = {
      def createFunction(option: Identifier, some: Identifier, value: Identifier): t.FunDef = {
        val get = ast.SymbolIdentifier("stainless.lang.Option.get")
        mkFunDef(get, t.Unchecked)("A") {
          case Seq(aT) => (Seq("x" :: T(option)(aT)), aT, {
            case Seq(v) => t.Require(v is some, v.getField(value))
          })
        }
      }

      val syntheticFunction: t.FunDef = {
        val some = syntheticOption.constructors.find(_.fields.nonEmpty).get
        createFunction(syntheticOption.id, some.id, some.fields.head.id)
      }

      val cache = new ExtractionCache[s.ADTSort, t.FunDef]
      (symbols: s.Symbols) => symbols.lookup.get[s.ADTSort]("stainless.lang.Option") match {
        case Some(sort) => cache.cached(sort, symbols) {
          val some = sort.constructors.find(_.fields.nonEmpty).get
          createFunction(sort.id, some.id, some.fields.head.id)
        }
        case None => syntheticGet(symbols)
      }
    }

    case class Info(option: Identifier, some: Identifier, none: Identifier,
                    isEmpty: Identifier, get: Identifier)

    def info(implicit symbols: s.Symbols): Info = {
      val optionSort = symbols.lookup.get[s.ADTSort]("stainless.lang.Option").getOrElse(syntheticOption)
      val some = optionSort.constructors.find(_.fields.nonEmpty).get.id
      val none = optionSort.constructors.find(_.fields.isEmpty).get.id

      val isEmpty = symbols.lookup.get[s.FunDef]("stainless.lang.Option.isEmpty")
        .getOrElse(syntheticIsEmpty(symbols)).id
      val get = symbols.lookup.get[s.FunDef]("stainless.lang.Option.get")
        .getOrElse(syntheticGet(symbols)).id

      Info(optionSort.id, some, none, isEmpty, get)
    }

    def sorts(implicit symbols: s.Symbols): Seq[t.ADTSort] =
      symbols.lookup.get[s.ADTSort]("stainless.lang.Option") match {
        case Some(_) => Seq()
        case None => Seq(syntheticOption)
      }

    def functions(implicit symbols: s.Symbols): Seq[t.FunDef] =
      (symbols.lookup.get[s.FunDef]("stainless.lang.Option.isEmpty") match {
        case Some(_) => Seq()
        case None => Seq(syntheticIsEmpty(symbols))
      }) ++ (symbols.lookup.get[s.FunDef]("stainless.lang.Option.get") match {
        case Some(_) => Seq()
        case None => Seq(syntheticGet(symbols))
      })
  }
}
