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

  sealed trait TileBase
  object TileBase {
    case class FlatTerrain(base: BaseTerrain) extends TileBase
    case class HillTerrain(base: BaseTerrain) extends TileBase
    case object Mountain extends TileBase
    case object Lake extends TileBase
    case object Coast extends TileBase
    case object Ocean extends TileBase
  }

  sealed trait BaseTerrain
  object BaseTerrain {
    case object Plains extends BaseTerrain
    case object Grassland extends BaseTerrain
    case object Desert extends BaseTerrain
    case object Tundra extends BaseTerrain
    case object Snow extends BaseTerrain
  }

  sealed trait Feature
  object Feature {
    case object Forest extends Feature
    case object RainForest extends Feature
    case object Marsh extends Feature
    // etc.
  }

  sealed trait Resource
  object Resource {
    case object Iron extends Resource // can't make Stainless Steel without Iron, so this must be here
    case object Wheat extends Resource
    case object Rice extends Resource
    case object Stone extends Resource
    case object Crabs extends Resource
    case object Fish extends Resource
    case object Coal extends Resource
    // etc.
  }

  sealed trait Construction
  object Construction {
    case class City(id: BigInt) extends Construction
    case class District(kind: DistrictKind) extends Construction
    case class Exploitation(kind: ResourceImprovement) extends Construction
  }

  sealed trait DistrictKind
  object DistrictKind {
    case object Campus extends DistrictKind
    case object IndustrialZone extends DistrictKind
    // etc.
  }

  sealed trait ResourceImprovement
  object ResourceImprovement {
    case object Farm extends ResourceImprovement
    case object Fishery extends ResourceImprovement
    case object Mine extends ResourceImprovement
    case object Quarry extends ResourceImprovement
    // etc.
  }
}