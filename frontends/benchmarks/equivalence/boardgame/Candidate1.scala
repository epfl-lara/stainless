import stainless.lang._
import stainless.collection._
import defs._

object Candidate1 {

  def adjacencyBonus(wm: WorldMap, x: BigInt, y: BigInt, districtKind: DistrictKind): BigInt = {
    require(0 <= y && y < wm.height)
    require(wm.width > 4)
    def adj(tile: Tile): BigInt = {
      districtKind match {
        case DistrictKind.Campus => tile.base match {
          case TileBase.Mountain => BigInt(2)
          case _ => tile.construction match {
            case Some(Construction.City(_))  => BigInt(1)
            case Some(Construction.District(_)) => BigInt(1)
            case _ => BigInt(0)
          }
        }
        case DistrictKind.IndustrialZone =>
          val resAdj = tile.resource match {
            case Some(Resource.Iron) => BigInt(2)
            case Some(Resource.Coal) => BigInt(2)
            case _ => BigInt(0)
          }
          tile.construction match {
            case Some(Construction.City(_)) => resAdj + BigInt(1)
            case Some(Construction.District(_)) => resAdj + BigInt(1)
            case Some(Construction.Exploitation(ResourceImprovement.Mine)) => resAdj + BigInt(1)
            case Some(Construction.Exploitation(ResourceImprovement.Quarry)) => resAdj + BigInt(2)
            case _ => resAdj
          }
      }
    }
    def sum(ts: List[Tile], acc: BigInt): BigInt = {
      decreases(ts)
      ts match {
        case Nil() => acc
        case Cons(tile, rest) => sum(rest, acc + adj(tile))
      }
    }
    sum(collectTilesInRing(wm, x, y, 1), 0)
  }

  ///////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////

  def validCitySettlement(wm: WorldMap, x: BigInt, y: BigInt): Boolean = {
    require(0 <= y && y < wm.height)
    require(wm.width > 4)
    noCitiesInHorizon(wm, x, y) && tileFreeForSettlement(wm, x, y)
  }

  /////////////////////////////////////

  def tileInWorld(wm: WorldMap, x: BigInt, y: BigInt): Tile = {
    require(0 <= y && y < wm.height)
    val xx = (x % wm.width + wm.width) % wm.width
    val ix = y * wm.width + xx
    wm.tiles(ix)
  }

  def tileFreeForSettlement(wm: WorldMap, x: BigInt, y: BigInt): Boolean = {
    require(0 <= y && y < wm.height)
    val tile = tileInWorld(wm, x, y)
    (tile.base match {
      case TileBase.FlatTerrain(_) => true
      case TileBase.HillTerrain(_) => true
      case _ => false
    }) && (tile.construction match {
      case Some(Construction.City(_)) => false
      case Some(Construction.District(_)) => false
      case None() => true
      case Some(Construction.Exploitation(_)) => true
    })
  }

  def noCitiesInHorizon(wm: WorldMap, x: BigInt, y: BigInt): Boolean = {
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
    loop(collectTilesWithinRadius(wm, x, y, 2))
  }

  def collectTilesWithinRadius(wm: WorldMap, x: BigInt, y: BigInt, radius: BigInt): List[Tile] = {
    require(0 <= y && y < wm.height)
    require(radius >= 0)
    require(2 * radius < wm.width)

    def allRings(currRadius: BigInt): List[Tile] = {
      decreases(radius - currRadius)
      require(0 <= currRadius && currRadius <= radius)
      val atThisRadius = collectTilesInRing(wm, x, y, currRadius)
      if (currRadius == radius) atThisRadius
      else atThisRadius ++ allRings(currRadius + 1)
    }

    allRings(0)
  }

  def collectTilesInRing(wm: WorldMap, x: BigInt, y: BigInt, ring: BigInt): List[Tile] = {
    require(0 <= y && y < wm.height)
    require(ring >= 0)
    require(2 * ring < wm.width)

    def loop(i: BigInt): List[Tile] = {
      require(ring > 0)
      require(0 <= i && i < 6 * ring)
      decreases(6 * ring - i)

      val corner = i / ring
      val rest = i % ring
      val diffX = {
        if (corner == 0) rest
        else if (corner == 1) ring
        else if (corner == 2) ring - rest
        else if (corner == 3) -rest
        else if (corner == 4) -ring
        else rest - ring
      }
      val diffY = {
        if (corner == 0) ring - rest
        else if (corner == 1) -rest
        else if (corner == 2) -ring
        else if (corner == 3) rest - ring
        else if (corner == 4) rest
        else ring
      }

      val xx = x + diffX
      val yy = y + diffY
      val includeThis = {
        if (0 <= yy && yy < wm.height) List(tileInWorld(wm, xx, yy))
        else Nil[Tile]()
      }
      if (i == 6 * ring - 1) includeThis
      else includeThis ++ loop(i + 1)
    }
    if (ring > 0) loop(0)
    else List(tileInWorld(wm, x, y))
  }

}