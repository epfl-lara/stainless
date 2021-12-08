/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package utils

trait SyntheticSorts extends ExtractionCaches { self: CachingPhase =>

  protected object OptionSort {
    import t._
    import t.dsl._

    private[this] val syntheticOption: t.ADTSort = {
      val Seq(option, some, none) =
        Seq("Option", "Some", "None").map(name => ast.SymbolIdentifier("stainless.internal." + name))
      val value = FreshIdentifier("value")
      mkSort(option)("A") { case Seq(aT) => Seq((some, Seq(t.ValDef(value, aT))), (none, Seq())) }
    }

    private[this] val syntheticIsEmpty: s.Symbols => t.FunDef = {
      def createFunction(option: Identifier, none: Identifier): t.FunDef = {
        val isEmpty = ast.SymbolIdentifier("stainless.internal.Option.isEmpty")
        mkFunDef(isEmpty, t.DropVCs, t.Synthetic)("A") {
          case Seq(aT) => (Seq("x" :: T(option)(aT)), t.BooleanType(), { case Seq(v) => v is none })
        }
      }

      val syntheticFunction: t.FunDef = createFunction(
        syntheticOption.id,
        syntheticOption.constructors.find(_.fields.isEmpty).get.id)

      val cache = new SimpleCache[s.ADTSort, t.FunDef]
      (symbols: s.Symbols) => symbols.lookup.get[s.ADTSort]("stainless.internal.Option") match {
        case Some(sort) => cache.cached(sort) {
          createFunction(sort.id, sort.constructors.find(_.fields.isEmpty).get.id)
        }
        case None => syntheticFunction
      }
    }

    private[this] val syntheticGet: s.Symbols => t.FunDef = {
      def createFunction(option: Identifier, some: Identifier, value: Identifier): t.FunDef = {
        val get = ast.SymbolIdentifier("stainless.internal.Option.get")
        mkFunDef(get, t.DropVCs, t.Synthetic)("A") {
          case Seq(aT) => (Seq("x" :: T(option)(aT)), aT, {
            case Seq(v) => t.Require(v is some, v.getField(value))
          })
        }
      }

      val syntheticFunction: t.FunDef = {
        val some = syntheticOption.constructors.find(_.fields.nonEmpty).get
        createFunction(syntheticOption.id, some.id, some.fields.head.id)
      }

      val cache = new SimpleCache[s.ADTSort, t.FunDef]
      (symbols: s.Symbols) => symbols.lookup.get[s.ADTSort]("stainless.internal.Option") match {
        case Some(sort) => cache.cached(sort) {
          val some = sort.constructors.find(_.fields.nonEmpty).get
          createFunction(sort.id, some.id, some.fields.head.id)
        }
        case None => syntheticFunction
      }
    }

    private[this] def optionSort(using symbols: s.Symbols): inox.ast.Trees#ADTSort =
      symbols.lookup.get[s.ADTSort]("stainless.internal.Option").getOrElse(syntheticOption)

    def option(using s.Symbols): Identifier = optionSort.id
    def some(using s.Symbols): Identifier = optionSort.constructors.find(_.fields.nonEmpty).get.id
    def none(using s.Symbols): Identifier = optionSort.constructors.find(_.fields.isEmpty).get.id

    def value(using s.Symbols): Identifier = optionSort.constructors.flatMap(_.fields).head.id

    def isEmpty(using symbols: s.Symbols): Identifier =
      symbols.lookup.get[s.FunDef]("stainless.internal.Option.isEmpty").getOrElse(syntheticIsEmpty(symbols)).id
    def get(using symbols: s.Symbols): Identifier =
      symbols.lookup.get[s.FunDef]("stainless.internal.Option.get").getOrElse(syntheticGet(symbols)).id

    def sorts(using symbols: s.Symbols): Seq[t.ADTSort] =
      symbols.lookup.get[s.ADTSort]("stainless.internal.Option") match {
        case Some(_) => Seq()
        case None => Seq(syntheticOption)
      }

    def functions(using symbols: s.Symbols): Seq[t.FunDef] =
      (symbols.lookup.get[s.FunDef]("stainless.internal.Option.isEmpty") match {
        case Some(_) => Seq()
        case None => Seq(syntheticIsEmpty(symbols))
      }) ++ (symbols.lookup.get[s.FunDef]("stainless.internal.Option.get") match {
        case Some(_) => Seq()
        case None => Seq(syntheticGet(symbols))
      })

    def key(using symbols: s.Symbols): CacheKey = new SeqKey(
      symbols.lookup.get[s.ADTSort]("stainless.internal.Option").map(SortKey(_)).toSeq ++
      symbols.lookup.get[s.FunDef]("stainless.internal.Option.isEmpty").map(FunctionKey(_)) ++
      symbols.lookup.get[s.FunDef]("stainless.internal.Option.get").map(FunctionKey(_))
    )
  }


  // ControlFlowSort represents the following class:
  // sealed abstract class ControlFlow[Ret, Cur]
  // case class Return[Ret, Cur](value: Ret)  extends ControlFlow[Ret, Cur]
  // case class Proceed[Ret, Cur](value: Cur) extends ControlFlow[Ret, Cur]
  protected object ControlFlowSort {
    import t._
    import t.dsl._

    val syntheticControlFlow: t.ADTSort = {
      val Seq(controlFlow, ret, proceed) =
        Seq("ControlFlow", "Return", "Proceed").map(name => ast.SymbolIdentifier("stainless.internal." + name))
      val retValue = FreshIdentifier("value")
      val proceedValue = FreshIdentifier("value")
      mkSort(controlFlow)("Ret", "Cur") { case Seq(retT, curT) =>
        Seq(
          (ret, Seq(t.ValDef(retValue, retT))),
          (proceed, Seq(t.ValDef(proceedValue, curT)))
        )
      }
    }

    val controlFlowId: Identifier = syntheticControlFlow.id
    val retId: Identifier = syntheticControlFlow.constructors.find(_.id.name == "Return").get.id
    val proceedId: Identifier = syntheticControlFlow.constructors.find(_.id.name == "Proceed").get.id

    object Return {
      def unapply(e: Expr): Option[Expr] = e match {
        case ADT(`retId`, Seq(_, _), Seq(arg)) => Some(arg)
        case _ => None
      }
    }

    object Proceed {
      def unapply(e: Expr): Option[Expr] = e match {
        case ADT(`proceedId`, Seq(_, _), Seq(arg)) => Some(arg)
        case _ => None
      }
    }

    def controlFlow(retT: Type, curT: Type): Type = ADTType(controlFlowId, Seq(retT, curT))
    def ret(retT: Type, curT: Type, e: Expr) = ADT(retId, Seq(retT, curT), Seq(e)).setPos(e)
    def proceed(retT: Type, curT: Type, e: Expr) = ADT(proceedId, Seq(retT, curT), Seq(e)).setPos(e)

    def buildMatch(
      retT: Type, curT: Type,
      scrut: Expr,
      retCase: Variable => Expr,
      proceedCase: Variable => Expr,
      pos: inox.utils.Position
    ): Expr = {
      val retVal = ValDef.fresh("retValue", retT).setPos(pos)
      val proceedVal = ValDef.fresh("proceedValue", curT).setPos(pos)
      MatchExpr(scrut, Seq(
        MatchCase(
          ADTPattern(None, retId, Seq(retT, curT), Seq(WildcardPattern(Some(retVal)))).setPos(pos),
          None,
          retCase(retVal.toVariable)
        ).setPos(pos),
        MatchCase(
          ADTPattern(None, proceedId, Seq(retT, curT), Seq(WildcardPattern(Some(proceedVal)))).setPos(pos),
          None,
          proceedCase(proceedVal.toVariable)
        ).setPos(pos),
      )).setPos(pos)
    }

    def andThen(retT: Type, curT: Type, nextT: Type, previous: Expr, next: Variable => Expr, pos: inox.utils.Position): Expr = {
      buildMatch(retT, curT, previous,
        rv => ret(retT, nextT, rv),
        next,
        pos
      )
    }
  }
}
