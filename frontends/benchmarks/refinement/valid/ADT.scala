case class Same(x: Int, y: Int with x==y)

def same = Same(2, 2)