package oldInRefinement

import stainless.lang._

case class Box(var value: BigInt)

def incrementBox(b: Box): {res: Unit with b.value == old(b).value + 1} = b.value += 1

def incrementBy(b: Box, k: BigInt): {res: Unit with b.value == old(b).value + k} = b.value += k

case class Box2(var value: BigInt):
  def getValue(): BigInt = value
  def increment(): {res: Unit with getValue() == old(this).getValue() + 1} = value += 1
