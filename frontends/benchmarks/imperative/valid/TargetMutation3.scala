import stainless._
import stainless.lang._

object TargetMutation3 {

  case class Box(var value: Int)

  def mutate(b: Box, v: Int): Unit = {
    b.value = v;
  }

  def badManners(arr: Array[Box], otherArr: Array[Box], b1: Box, b2: Box, b3: Box, cond1: Boolean, cond2: Boolean, i: Int): Unit = {
    require(0 <= i && i < 2000)
    require(arr.length >= 3000)

    val oldi0 = arr(i).value
    val oldi1 = arr(i + 1).value
    val oldi2 = arr(i + 2).value
    val oldi3 = arr(i + 3).value
    val oldi4 = arr(i + 4).value
    val oldi5 = arr(i + 5).value
    val oldi6 = arr(i + 6).value

    val aliasArr = arr
    var ii = i
    ii += 1

    val aliasedElem = arr(ii)
    arr(ii).value = 123

    assert(arr(i).value == oldi0)
    assert(arr(ii).value == 123)
    assert(aliasArr(i).value == oldi0)
    assert(aliasArr(ii).value == 123)
    assert(aliasedElem.value == 123)

    ii += 1
    arr(ii).value = 456
    assert(aliasedElem.value == 123) // Unaffected

    // :O what are you doing???
    arr({
      ii += 1
      mutate(b1, 11)
      ii
    }).value = 456

    assert(ii == i + 3)
    val iii = ii
    assert(b1.value == 11)
    assert(arr(ii).value == 456)
    assert(iii == ii)
    assert(iii == i + 3)

    // Please stop!!!
    arr({
      ii += 1
      mutate(if (cond1) b2 else b3, 22)
      ii
    }).value = 789

    // AAAAAAAAAAAA
    if (cond2) {
      val aliasedElem2 = arr(i + 2)
      assert(aliasedElem2.value == 456)
      aliasedElem2.value = 111
      ii += 2
    } else {
      // Here, we write ii0 for ii before entering this mayhem
      // arr(ii0).value == 789
      mutate({
        arr({
          mutate({
            ii += 1
            arr(ii)
          }, 333)
          // arr(ii0 + 1).value == 333
          ii += 1
          ii
        }).value = 0xbadbad
        // arr(ii0 + 2).value == 0xbadbad
        ii += 1
        arr(ii)
      }, 444)
      // arr(ii0 + 3).value == 444
    }
    assert(cond2 ==> (arr(i + 2).value == 111 && arr(ii - 1).value == oldi5 && arr(ii).value == oldi6))
    assert(!cond2 ==> (arr(ii).value == 444 && arr(ii - 1).value == 0xbadbad && arr(ii - 2).value == 333 && arr(ii - 3).value == 789))

    ii += 1
    mutate(arr(ii), 112233)
    assert(arr(ii).value == 112233)
    assert(aliasArr(ii).value == 112233)
    mutate(aliasArr(ii), 332211)
    assert(arr(ii).value == 332211)
    assert(aliasArr(ii).value == 332211)
    assert(aliasedElem.value == 123)
  }
}
