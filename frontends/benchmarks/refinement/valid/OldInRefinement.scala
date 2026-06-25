package oldInRefinement

import stainless.lang._

case class Box(var value: BigInt)

def incrementBox(b: Box): {res: Unit with b.value == old(b).value + 1} = b.value += 1

def incrementBy(b: Box, k: BigInt): {res: Unit with b.value == old(b).value + k} = b.value += k
