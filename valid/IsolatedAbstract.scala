import leon.Utils._
import leon.Annotations._

object LoneAbstract {

  /* 
   * create a structure with all these fields
   */
  sealed abstract class TrackedFields
  case class TreeFields(isBST: Boolean)

  /* add this structure to Tree class */
  sealed abstract class Tree
  case class Leaf(fields:TreeFields) extends Tree
  case class Node(left : Tree, value : Int, right: Tree, fields:TreeFields) extends Tree


  def foo(): Int = {
    42
  } ensuring ( _ > 0 )
}
