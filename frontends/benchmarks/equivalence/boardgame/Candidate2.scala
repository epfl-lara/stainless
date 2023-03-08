import stainless.lang._
import stainless.collection._
import defs._

object Candidate2 {

  def adjacencyBonus(wm: WorldMap, x: BigInt, y: BigInt, districtKind: DistrictKind): BigInt = {
    require(0 <= y && y < wm.height)
    adj(wm, x, y + 1, districtKind) +
      adj(wm, x + 1, y, districtKind) +
      adj(wm, x + 1, y - 1, districtKind) +
      adj(wm, x, y - 1, districtKind) +
      adj(wm, x - 1, y, districtKind) +
      adj(wm, x - 1, y + 1, districtKind)
  }

  def adj(wm: WorldMap, x: BigInt, y: BigInt, districtKind: DistrictKind): BigInt = {
    if (y < 0 || y >= wm.height) BigInt(0)
    else {
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
  }

  ///////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////

  def validCitySettlement(wm: WorldMap, x: BigInt, y: BigInt): Boolean = {
    require(0 <= y && y < wm.height)
    require(wm.width > 4)
    val tile = tileInWorld(wm, x, y)
    tile.base match {
      case TileBase.FlatTerrain(_) => true
      case TileBase.HillTerrain(_) => true
      case _ => false
    }
  }

  /////////////////////////////////////

  def tileInWorld(wm: WorldMap, x: BigInt, y: BigInt): Tile = {
    require(0 <= y && y < wm.height)
    val xx = (x % wm.width + wm.width) % wm.width
    val ix = y * wm.width + xx
    wm.tiles(ix)
  }
}