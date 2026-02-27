package refinementAssignmentPosAsInstanceOf

val z: Int = (-1).asInstanceOf[{v: Int with v > 0}]