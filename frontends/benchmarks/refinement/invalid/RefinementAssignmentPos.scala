type Pos = {v: Int with v > 0}

val z: Pos = (-1).asInstanceOf[Pos]