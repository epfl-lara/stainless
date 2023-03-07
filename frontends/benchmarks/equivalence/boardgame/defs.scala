import stainless.lang._
import stainless.collection._

object defs {

  case class Tile(
    base: TileBase,
    feature: Option[Feature],
    resource: Option[Resource],
    construction: Option[Construction]
  )

  // Hexagon tiles, cylinder world (i.e. wraps around x-axis)
  case class WorldMap(tiles: List[Tile], width: BigInt, height: BigInt) {
    require(width > 0 && height > 0)
    require(tiles.length == width * height)
  }

  enum TileBase {
    case FlatTerrain(base: BaseTerrain)
    case HillTerrain(base: BaseTerrain)
    case Mountain()
    case Lake()
    case Coast()
    case Ocean()
  }

  enum BaseTerrain {
    case Plains()
    case Grassland()
    case Desert()
    case Tundra()
    case Snow()
  }

  enum Feature {
    case Forest()
    case RainForest()
    case Marsh()
    // etc.
  }

  enum Resource {
    case Iron() // can't make Stainless Steel without Iron, so this must be here
    case Wheat()
    case Rice()
    case Stone() // weak
    case Crabs() // the best
    case Fish()
    case Coal() // cursed
    // etc.
  }

  enum Construction {
    case City(id: BigInt)
    case District(kind: DistrictKind)
    case Exploitation(kind: ResourceImprovement)
  }

  enum DistrictKind {
    case Campus()
    case IndustrialZone()
    // etc.
  }

  enum ResourceImprovement {
    case Farm()
    case Fishery()
    case Mine()
    case Quarry()
    // etc.
  }
}