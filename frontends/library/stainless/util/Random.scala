/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.util

import scala.language.implicitConversions

import stainless.annotation._

object Random {

  @library
  case class State(var seed: BigInt)

  @library
  def newState: State = State(0)

  @library
  @isabelle.noBody()
  def nextBoolean(implicit state: State): Boolean = {
    state.seed += 1
    nativeNextBoolean(state.seed)
  } ensuring((x: Boolean) => true)

  @library
  @extern
  private def nativeNextBoolean(seed: BigInt): Boolean = {
    scala.util.Random.nextBoolean
  } ensuring((x: Boolean) => true)



  @library
  @isabelle.noBody()
  def nextInt(implicit state: State): Int = {
    state.seed += 1
    nativeNextInt(state.seed)
  } ensuring((x: Int) => true)

  @library
  @extern
  private def nativeNextInt(seed: BigInt): Int = {
    scala.util.Random.nextInt
  } ensuring((x: Int) => true)



  @library
  @isabelle.noBody()
  def nextInt(max: Int)(implicit state: State): Int = {
    require(max > 0)
    state.seed += 1
    nativeNextInt(max)(state.seed)
  } ensuring(res => res >= 0 && res < max)

  @library
  @extern
  def nativeNextInt(max: Int)(seed: BigInt): Int = {
    scala.util.Random.nextInt(max)
  } ensuring(res => res >= 0 && res < max)



  @library
  @isabelle.noBody()
  def nextBigInt(implicit state: State): BigInt = {
    state.seed += 1
    nativeNextBigInt(state.seed)
  } ensuring((x: BigInt) => true)

  @library
  @extern
  private def nativeNextBigInt(seed: BigInt): BigInt = {
    BigInt(scala.util.Random.nextInt)
  } ensuring((x: BigInt) => true)



  @library
  @isabelle.noBody()
  def nextBigInt(max: BigInt)(implicit state: State): BigInt = {
    require(max > 0)
    state.seed += 1
    nativeNextBigInt(max, state.seed)
  } ensuring((res: BigInt) => res >= 0 && res < max)

  @library
  @extern
  private def nativeNextBigInt(max: BigInt, seed: BigInt): BigInt = {
    BigInt(scala.util.Random.nextInt(max.toInt))
  } ensuring((x: BigInt) => x >= 0 && x < max)

}
