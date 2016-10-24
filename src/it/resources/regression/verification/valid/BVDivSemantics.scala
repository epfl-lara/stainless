/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._
import leon._

object BVDivSemantics {

  def identity2(x: Int): Boolean = {
    require(x != -2147483648)
    -(x / 2) == -x/2
  } ensuring(res => res)

  def identity3(x: Int): Boolean = {
    -(x / 2) == x / -2
  } ensuring(res => res)

  //def identity4(x: Int, y: Int): Boolean = {
  //  require(y > 0)
  //  - (x % y) == (-x)%y
  //} ensuring(res => res)

  def identity5(x: Int): Boolean = {
    x % 2 == x % -2
  } ensuring(res => res)

  def identity6(x: Int): Boolean = {
    require(x != 0)
    5 % x == 5 % -x
  } ensuring(res => res)


  def basic1(): Boolean = {
    -3 / 2 == -1
  } ensuring(res => res)
  def basic2(): Boolean = {
    -3 / -2 == 1
  } ensuring(res => res)
  def basic3(): Boolean = {
    3 / -2 == -1
  } ensuring(res => res)
  def basic4(): Boolean = {
    3 % -2 == 1
  } ensuring(res => res)
  def basic5(): Boolean = {
    -3 % -2 == -1
  } ensuring(res => res)
  def basic6(): Boolean = {
    -3 % 2 == -1
  } ensuring(res => res)

}
