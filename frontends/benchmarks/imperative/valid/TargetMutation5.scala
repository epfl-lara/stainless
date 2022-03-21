import stainless._
import stainless.lang._

object TargetMutation5 {

  case class Box(var value1: Int, var value2: Int, var value3: Int)

  def mutate(b: Box, v: Int): Unit = {
    b.value1 = v;
  }

  def mmutate(b: Box, v1: Int, v2: Int): Unit = {
    b.value1 = v1;
    b.value2 = v2;
  }

  def t1(arr: Array[Box], i: Int): Unit = {
    require(0 <= i && i < 2000)
    require(arr.length >= 3000)

    val aliasArr = arr
    var ii = i
    ii += 1

    val aliasedElem = arr(ii)
    val elemOldVal2 = aliasedElem.value2
    val elemOldVal3 = aliasedElem.value3
    arr(ii).value1 = 123
    assert(arr(ii).value2 == elemOldVal2)
    assert(arr(ii).value3 == elemOldVal3)
    ii += 1

    // Mutating the "original array"
    val oldVal2 = arr(ii).value2
    val oldVal3 = arr(ii).value3
    mutate(arr(ii), 456)
    assert(arr(ii).value1 == 456)
    assert(arr(ii).value2 == oldVal2)
    assert(arr(ii).value3 == oldVal3)
    assert(aliasArr(ii).value1 == 456)
    assert(aliasArr(ii).value2 == oldVal2)
    assert(aliasArr(ii).value3 == oldVal3)
    assert(aliasedElem.value1 == 123)
    assert(aliasedElem.value2 == elemOldVal2)
    assert(aliasedElem.value3 == elemOldVal3)

    // Mutating the aliased array
    ii += 1
    val oldVal2Bis = arr(ii).value2
    val oldVal3Bis = arr(ii).value3
    mutate(aliasArr(ii), 789)
    assert(arr(ii).value1 == 789)
    assert(arr(ii).value2 == oldVal2Bis)
    assert(arr(ii).value3 == oldVal3Bis)
    assert(aliasArr(ii).value1 == 789)
    assert(aliasArr(ii).value2 == oldVal2Bis)
    assert(aliasArr(ii).value3 == oldVal3Bis)
    assert(aliasedElem.value1 == 123)
    assert(aliasedElem.value2 == elemOldVal2)
    assert(aliasedElem.value3 == elemOldVal3)
  }

  // Same as t1, but we mutate multiple fields through mmutate
  def t2(arr: Array[Box], i: Int): Unit = {
    require(0 <= i && i < 2000)
    require(arr.length >= 3000)

    val aliasArr = arr
    var ii = i
    ii += 1

    val aliasedElem = arr(ii)
    val elemOldVal2 = aliasedElem.value2
    val elemOldVal3 = aliasedElem.value3
    arr(ii).value1 = 123
    assert(arr(ii).value2 == elemOldVal2)
    assert(arr(ii).value3 == elemOldVal3)
    ii += 1

    // Mutating the "original array"
    val oldVal3 = arr(ii).value3
    mmutate(arr(ii), 456, -456)
    assert(arr(ii).value1 == 456)
    assert(arr(ii).value2 == -456)
    assert(arr(ii).value3 == oldVal3)
    assert(aliasArr(ii).value1 == 456)
    assert(aliasArr(ii).value2 == -456)
    assert(aliasArr(ii).value3 == oldVal3)
    assert(aliasedElem.value1 == 123)
    assert(aliasedElem.value2 == elemOldVal2)
    assert(aliasedElem.value3 == elemOldVal3)

    // Mutating the aliased array
    ii += 1
    val oldVal3Bis = arr(ii).value3
    mmutate(aliasArr(ii), 789, -789)
    assert(arr(ii).value1 == 789)
    assert(arr(ii).value2 == -789)
    assert(arr(ii).value3 == oldVal3Bis)
    assert(aliasArr(ii).value1 == 789)
    assert(aliasArr(ii).value2 == -789)
    assert(aliasArr(ii).value3 == oldVal3Bis)
    assert(aliasedElem.value1 == 123)
    assert(aliasedElem.value2 == elemOldVal2)
    assert(aliasedElem.value3 == elemOldVal3)
  }
}
