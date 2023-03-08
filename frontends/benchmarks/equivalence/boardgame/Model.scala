import stainless.lang._
import stainless.collection._
import stainless.annotation._
import defs._

object Model {

  // Part 1. Calculating adjacency bonus
  // Rules:
  //   -For an industrial zone:
  //      -Adjacent iron, coal or quarry: +1
  //      -Adjacent mine, city or district: +1/2
  //   -For a campus:
  //      -Adjacent mountain: +1
  //      -Adjacent city or district: +1/2
  // Since we have half point, the result is doubled to have integers
  def adjacencyBonus1(wm: WorldMap, x: BigInt, y: BigInt, districtKind: DistrictKind): BigInt = {
    require(0 <= y && y < wm.height)
    require(wm.width > 4)
    adj(wm, x, y + 1, districtKind) +
    adj(wm, x + 1, y, districtKind) +
    adj(wm, x + 1, y - 1, districtKind) +
    adj(wm, x, y - 1, districtKind) +
    adj(wm, x - 1, y, districtKind) +
    adj(wm, x - 1, y + 1, districtKind)
  }

  def adjacencyBonus2(wm: WorldMap, x: BigInt, y: BigInt, districtKind: DistrictKind): BigInt = {
    require(0 <= y && y < wm.height)
    require(wm.width > 4)

    def sum(acc: BigInt, ts: List[Tile]): BigInt = {
      decreases(ts)
      ts match {
        case Nil() => acc
        case Cons(tile, rest) => sum(acc + adj(tile, districtKind), rest)
      }
    }
    sum(0, collectTilesInRing(wm, x, y, 1))
  }

  def testsAdjacencyBonus: List[(WorldMap, BigInt, BigInt, DistrictKind)] = List(
    testsAdjacencyBonus1,
  )

  def testsAdjacencyBonus1: (WorldMap, BigInt, BigInt, DistrictKind) = {
    val G = Tile(TileBase.FlatTerrain(BaseTerrain.Grassland), None(), None(), None())
    val M = Tile(TileBase.Mountain, None(), None(), None())
    val X = G // The emplacement where we would like to compute for potential adjacency
    val wm = List(
            G, M, X, M, G,
          G, G, G, M, G,
        G, M, G, G, G,
      G, G, G, G, G,
    )
    // Note: the coordinates are upside down
    (WorldMap(wm, 5, 4), 2, 0, DistrictKind.Campus)
  }

  //////////////////////

  def adj(wm: WorldMap, x: BigInt, y: BigInt, districtKind: DistrictKind): BigInt = {
    if (y < 0 || y >= wm.height) BigInt(0)
    else adj(tileInWorld(wm, x, y), districtKind)
  }

  def adj(tile: Tile, districtKind: DistrictKind): BigInt = {
    (districtKind, tile) match {
      case (DistrictKind.Campus, Tile(TileBase.Mountain, _, _, _)) => BigInt(2)
      case (DistrictKind.Campus, Tile(_, _, _, Some(Construction.City(_)))) => BigInt(1)
      case (DistrictKind.Campus, Tile(_, _, _, Some(Construction.District(_)))) => BigInt(1)
      case (DistrictKind.Campus, _) => BigInt(0)
      case (DistrictKind.IndustrialZone, Tile(_, _, res, ctor)) =>
        val resAdj = res match {
          case Some(Resource.Iron) => BigInt(2)
          case Some(Resource.Coal) => BigInt(2)
          case _ => BigInt(0)
        }
        val resCtor = ctor match {
          case Some(Construction.City(_)) => BigInt(1)
          case Some(Construction.District(_)) => BigInt(1)
          case Some(Construction.Exploitation(ResourceImprovement.Mine)) => BigInt(1)
          case Some(Construction.Exploitation(ResourceImprovement.Quarry)) => BigInt(2)
          case _ => BigInt(0)
        }
        resAdj + resCtor
    }
  }

  ///////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////

  // Part 2. Determining whether a placement is suitable for settling
  // -Rules: no other city in a 2-tile range
  // -The tile must be adequate for settling (flat or hill terrain, and must not have another city or district on it)
  def validCitySettlement(wm: WorldMap, x: BigInt, y: BigInt): Boolean = {
    require(0 <= y && y < wm.height)
    require(wm.width > 4)
    tileOkForCity(wm, x, y) && noOtherCitiesInRange(wm, x, y)
  }

  def testsValidCitySettlement: List[(WorldMap, BigInt, BigInt)] = List(
    testValidCitySettlement1,
    testValidCitySettlement2,
    testValidCitySettlement3,
  )

  def testValidCitySettlement1: (WorldMap, BigInt, BigInt) = {
    // Ok, can be settled
    val G = Tile(TileBase.FlatTerrain(BaseTerrain.Grassland), None(), None(), None())
    val X = G // where we would like to settle
    val wm = List(
            G, G, G, G, G,
          G, G, G, G, G,
        G, X, G, G, G,
      G, G, G, G, G,
    )
    // Note: the coordinates are upside down
    (WorldMap(wm, 5, 4), 1, 2)
  }

  def testValidCitySettlement2: (WorldMap, BigInt, BigInt) = {
    // A lake in the center, we can't settle there
    val G = Tile(TileBase.FlatTerrain(BaseTerrain.Grassland), None(), None(), None())
    val L = Tile(TileBase.Lake, None(), None(), None())
    val wm = List(
          G, G, G, G, G,
        G, G, L, G, G,
      G, G, G, G, G,
    )
    // Note: the coordinates are upside down
    (WorldMap(wm, 5, 3), 2, 1)
  }

  def testValidCitySettlement3: (WorldMap, BigInt, BigInt) = {
    // A city in the second ring of the place where we want to settle
    val G = Tile(TileBase.FlatTerrain(BaseTerrain.Grassland), None(), None(), None())
    val X = G // where we would like to settle
    val Y = Tile(TileBase.FlatTerrain(BaseTerrain.Grassland), None(), None(), Some(Construction.City(42))) // Oh no, someone's already there :(
    val wm = List(
            G, G, Y, G, G,
          G, G, G, G, G,
        G, X, G, G, G,
      G, G, G, G, G,
    )
    // Note: the coordinates are upside down
    (WorldMap(wm, 5, 4), 1, 2)
  }

  ///////////////////////////////////////////////////////////////////////////

  def tileOkForCity(wm: WorldMap, x: BigInt, y: BigInt): Boolean = {
    require(0 <= y && y < wm.height)
    val tile = tileInWorld(wm, x, y)
    val baseOk = tile.base match {
      case TileBase.FlatTerrain(_) => true
      case TileBase.HillTerrain(_) => true
      case _ => false
    }
    val ctorOk = tile.construction match {
      case None() => true
      case Some(Construction.Exploitation(_)) => true // res. improvement removed on settling
      case Some(Construction.District(_)) => false
      case Some(Construction.City(_)) => false
    }
    baseOk && ctorOk
  }

  def noOtherCitiesInRange(wm: WorldMap, x: BigInt, y: BigInt): Boolean = {
    require(0 <= y && y < wm.height)
    require(wm.width > 4)
    def loop(ls: List[Tile]): Boolean = {
      decreases(ls)
      ls match {
        case Cons(t, rest) => t.construction match {
          case Some(Construction.City(_)) => false
          case _ => loop(rest)
        }
        case Nil() => true
      }
    }
    loop(allTilesWithinRadius(wm, x, y, 2))
  }

  // Note: includes the x,y tile as well
  def allTilesWithinRadius(wm: WorldMap, x: BigInt, y: BigInt, radius: BigInt): List[Tile] = {
    require(0 <= y && y < wm.height)
    require(radius >= 0)
    require(2 * radius < wm.width) // To avoid repetition of tiles due to wrapping

    def allRings(currRadius: BigInt): List[Tile] = {
      decreases(radius - currRadius)
      require(0 <= currRadius && currRadius <= radius)
      val atThisRadius = collectTilesInRing(wm, x, y, currRadius)
      if (currRadius == radius) atThisRadius
      else atThisRadius ++ allRings(currRadius + 1)
    }

    allRings(0)
  }

  def collectTilesInRing(wm: WorldMap, x: BigInt, y: BigInt, radius: BigInt): List[Tile] = {
    require(0 <= y && y < wm.height)
    require(radius >= 0)
    require(2 * radius < wm.width)

    def loop(i: BigInt): List[Tile] = {
      require(radius > 0)
      require(0 <= i && i < 6 * radius)
      decreases(6 * radius - i)

      val corner = i / radius
      val rest = i % radius
      val diffX = {
        if (corner == 0) rest
        else if (corner == 1) radius
        else if (corner == 2) radius - rest
        else if (corner == 3) -rest
        else if (corner == 4) -radius
        else rest - radius
      }
      val diffY = {
        if (corner == 0) radius - rest
        else if (corner == 1) -rest
        else if (corner == 2) -radius
        else if (corner == 3) rest - radius
        else if (corner == 4) rest
        else radius
      }

      val xx = x + diffX
      val yy = y + diffY
      val includeThis = {
        if (0 <= yy && yy < wm.height) List(tileInWorld(wm, xx, yy))
        else Nil[Tile]()
      }
      if (i == 6 * radius - 1) includeThis
      else includeThis ++ loop(i + 1)
    }
    if (radius == 0) List(tileInWorld(wm, x, y))
    else loop(0)
  }

  // Note: Using extension method here on wm will create a match with candidates `tileInWorld`.
  // Since we must be Scala 2-compatible, we could be tempted in having an implicit class.
  // However, the signature will be different to candidates `tileInWorld` (leading to equiv. checking resulting in unknown)
  // As such, we use a plain function...
  def tileInWorld(wm: WorldMap, x: BigInt, y: BigInt): Tile = {
    require(0 <= y && y < wm.height)
    val xx = (x % wm.width + wm.width) % wm.width
    val ix = y * wm.width + xx
    wm.tiles(ix)
  }
}