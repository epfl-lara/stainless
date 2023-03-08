import stainless.lang._
import stainless.collection._
import defs._

object Candidate4 {

  def adjacencyBonus(wm: WorldMap, x: BigInt, y: BigInt, districtKind: DistrictKind): BigInt = {
    require(0 <= y && y < wm.height)
    require(wm.width > 4)
    // No, one must still compute adjacency even for tiles on the y-border of the map
    if (0 < y && y < wm.height - 1) {
      adj(wm, x, y + 1, districtKind) +
        adj(wm, x + 1, y, districtKind) +
        adj(wm, x + 1, y - 1, districtKind) +
        adj(wm, x, y - 1, districtKind) +
        adj(wm, x - 1, y, districtKind) +
        adj(wm, x - 1, y + 1, districtKind)
    } else BigInt(0)
  }

  def adj(wm: WorldMap, x: BigInt, y: BigInt, districtKind: DistrictKind): BigInt = {
    require(0 <= y && y < wm.height)
    val tile = tileInWorld(wm, x, y)
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

  ///////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////

  def validCitySettlement(wm: WorldMap, x: BigInt, y: BigInt): Boolean = {
    require(0 <= y && y < wm.height)
    require(wm.width > 4)
    // Desperately trying to do that by-hand, but forgets about the second ring...
    val (p1x, p1y) = (x, y + 1)
    val (p2x, p2y) = (x + 1, y)
    val (p3x, p3y) = (x + 1, y - 1)
    val (p4x, p4y) = (x, y - 1)
    val (p5x, p5y) = (x - 1, y)
    val (p6x, p6y) = (x - 1, y + 1)
    tileFreeForSettlement(wm, x, y) && notACity(wm, p1x, p1y) &&
      notACity(wm, p2x, p2y) &&
      notACity(wm, p3x, p3y) &&
      notACity(wm, p4x, p4y) &&
      notACity(wm, p5x, p5y) &&
      notACity(wm, p6x, p6y)
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
    }) && notACity(wm, x, y) && notADistrict(wm, x, y)
  }

  def notACity(wm: WorldMap, x: BigInt, y: BigInt): Boolean = {
    !(0 <= y && y < wm.height) || {
      val tile = tileInWorld(wm, x, y)
      tile.construction match {
        case Some(Construction.City(_)) => false
        case Some(Construction.District(_)) => true
        case Some(Construction.Exploitation(_)) => true
        case None() => true
      }
    }
  }
  def notADistrict(wm: WorldMap, x: BigInt, y: BigInt): Boolean = {
    !(0 <= y && y < wm.height) || {
      val tile = tileInWorld(wm, x, y)
      tile.construction match {
        case Some(Construction.District(_)) => false
        case Some(Construction.City(_)) => true
        case Some(Construction.Exploitation(_)) => true
        case None() => true
      }
    }
  }
}