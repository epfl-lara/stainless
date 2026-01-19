/* Copyright 2009-2025 EPFL, Lausanne */

package stainless.collection

import scala.reflect.ClassTag
import scala.compiletime.uninitialized
import stainless.annotation.*
import stainless.lang.StaticChecks.*
import stainless.lang.*
import stainless.collection.{List, Cons, Nil}

@library
/**
 * An immutable, array-backed collection providing efficient slice operations.
 * 
 * IArray is designed for use in verification, supporting reasoning via List semantics.
 * It exposes a subset of array operations, but is immutable and safe for verification.
 * Slicing and element access are efficient, and the underlying data is never mutated.
 *
 * @param innerList The underlying immutable list used as specification.
 * @tparam T The type of elements contained in the array.
 */
case class IArray[T: ClassTag](@ghost private val innerList: List[T]):
  require(innerList.size <= Int.MaxValue)

  @ignore
  var _arr: Array[T] = uninitialized
  @ignore
  var _offset: Int = uninitialized
  @ignore
  var _size: BigInt = uninitialized    

  @ghost
  def list: List[T] = this.innerList

  @pure @extern 
  def size: BigInt = {
    _size
  }.ensuring(_ == list.size)  

  @pure @extern 
  def isize: Int = {
    _size.toInt
  }.ensuring(_ == list.isize) 

  @pure @extern 
  def apply(i: BigInt): T = {
    require(0 <= i && i < size)
    _arr(_offset + i.toInt)
  }.ensuring(_ == list.apply(i))

  @pure @extern
  def slice(from: BigInt, until: BigInt): IArray[T] = {
    require(0 <= from && from <= until && until <= size)
    @ghost val list = this.list.slice(from, until)
    val res = IArray(list)
    res._arr = this._arr // _arr is never mutated
    res._offset = this._offset + from.toInt
    res._size = until - from
    res
  }.ensuring(_ == IArray(list.slice(from, until)))

  @pure @extern
  def concat(other: IArray[T]): IArray[T] = {
    require(this.size + other.size <= Int.MaxValue)
    @ghost val list = this.list ++ other.list
    val res = IArray(list)
    val newArr = new Array[T](this.size.toInt + other.size.toInt)
    java.lang.System.arraycopy(this._arr, this._offset, newArr, 0, this._size.toInt)
    java.lang.System.arraycopy(other._arr, other._offset, newArr, this.size.toInt, other._size.toInt)
    res._arr = newArr
    res._offset = 0
    res._size = this.size + other.size
    res
  }.ensuring(_ == IArray(this.list ++ other.list))

  @pure @extern
  def append(x: T): IArray[T] = {
    require(this.size + 1 <= Int.MaxValue)
    @ghost val list = this.list :+ x
    val res = IArray(list)

    res._arr = new Array[T](this.size.toInt + 1)
    java.lang.System.arraycopy(this._arr, this._offset, res._arr, 0, this._size.toInt)
    res._arr(this.size.toInt) = x
    res._offset = 0
    res._size = this.size + 1
    res
  }.ensuring(_ == IArray(this.list :+ x))

  @pure @extern
  def contains(x: T): Boolean = {
    var found = false
    var i: BigInt = 0
    val endI: BigInt = this._size
    while i < endI && !found do
      if apply(i) == x then found = true
      i += 1
    found
  }.ensuring(_ == list.contains(x))

  @pure @extern
  def forall(p: T => Boolean): Boolean = {
    var res = true
    var i: BigInt = 0
    val endI: BigInt = this._size
    while i < endI && res do
      if !p(apply(i)) then res = false
      i += 1
    res
  }.ensuring(_ == list.forall(p))
  
  @pure @extern
  def exists(p: T => Boolean): Boolean = {
    var res = false
    var i: BigInt = 0
    val endI: BigInt = this._size
    while i < endI && !res do
      if p(apply(i)) then res = true
      i += 1
    res
  }.ensuring(_ == list.exists(p))

  @pure @extern
  def map[B: ClassTag](f: T => B): IArray[B] = {
    @ghost val list = this.list.map(f)
    val res = IArray(list)
    res._arr = new Array[B](this._size.toInt)
    var i: BigInt = 0
    while i < this.size do
      res._arr(i.toInt) = f(this.apply(i))
      i += 1
    res._offset = 0
    res._size = this._size
    res
  }.ensuring(_ == IArray(this.list.map(f)))

  @pure @extern
  def filter(p: T => Boolean): IArray[T] = {
    @ghost val list = this.list.filter(p)
    val res = IArray(list)
    val toKeep = new Array[Boolean](this._size.toInt)
    var count: BigInt = 0
    var i: BigInt = 0
    while i < this._size do
      if p(this.apply(i)) then
        toKeep(i.toInt) = true
        count += 1
      else toKeep(i.toInt) = false
      i += 1
    res._arr = new Array[T](count.toInt)
    var j: BigInt = 0
    i = 0
    while i < this._size do
      if toKeep(i.toInt) then
        res._arr(j.toInt) = this.apply(i)
        j += 1
      i += 1
    res._offset = 0
    res._size = count
    res
  }.ensuring(_ == IArray(this.list.filter(p)))

  @pure @extern
  def last: T = {
    require(this.size > 0)
    this.apply(this.size - 1)
  }.ensuring(_ == this.list.last)
  
@library
object IArray:
  @pure @extern
  def empty[T: ClassTag](): IArray[T] = {
    val res = IArray[T](Nil())
    res._arr = new Array[T](0)
    res._offset = 0
    res._size = 0
    res
  }.ensuring(_ == IArray[T](Nil()))
  
  @pure @extern
  def fill[T: ClassTag](n: BigInt)(x: T): IArray[T] = {
    require(0 <= n && n <= Int.MaxValue)
    @ghost val list = List.fill(n)(x)
    val res = IArray(list)      
    res._arr = Array.fill[T](n.toInt)(x)
    res._offset = 0
    res._size = n
    res      
  }.ensuring(_ == IArray(List.fill(n)(x)))
  
  @ghost
  def range(from: BigInt, until: BigInt): List[BigInt] = {
    require(0 <= from && from <= until && until <= Int.MaxValue)
    decreases(until - from)
    if(until <= from) stainless.collection.Nil[BigInt]() 
    else 
      val tl = range(from + 1, until)
      Cons(from, tl)
  }.ensuring(_.size == until - from)

  @pure @extern
  def tabulate[T: ClassTag](n: BigInt)(f: BigInt => T): IArray[T] = {
    require(0 <= n && n <= Int.MaxValue)
    @ghost val list = range(0, n).map(f)
    val res: IArray[T] = IArray(list)
    res._arr = Array.tabulate[T](n.toInt)(i => f(BigInt(i)))
    res._offset = 0
    res._size = n
    res
  }.ensuring(_ == IArray(range(0, n).map(f)))

end IArray
