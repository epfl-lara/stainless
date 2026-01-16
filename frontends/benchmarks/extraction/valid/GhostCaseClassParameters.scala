// see https://github.com/epfl-lara/stainless/issues/1670
import stainless.annotation.*
object GhostParameters: 
  case class C(@ghost x: Int):  
    def cp: C = {
      @ghost val x1 : Int = 3
      C(x1)
    }