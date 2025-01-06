import stainless.annotation._

object ClassReconstruction {

  case class BoundedCounter(var counter: BigInt, var bound: BigInt) {
    require(0 <= counter && counter < bound)

    @opaque // Note the opaque
    def bcTryAdd(i: BigInt): Unit = {
      if (0 <= i && counter + i < bound) {
        counter += i
      }
    }
  }

  @mutable
  trait BoundedCounterContainer {
    val boundedCounter: BoundedCounter

    final def tryAdd(i: BigInt): Unit = {
      boundedCounter.bcTryAdd(i)
    }

    final def tryAdd2(i: BigInt): Unit = {
      // After AntiAliasing, `tryAdd2` is as follows:
      //
      //   var thiss: BoundedCounterContainer = thiss
      //   ({
      //     var res: (Unit, BoundedCounterContainer) = tryAdd(thiss, i)
      //     thiss = @DropVCs (if (res._2.isInstanceOf[BoundedCounterContainerExt]) {
      //        @DropVCs BoundedCounterContainerExt(
      //          @DropVCs thiss.asInstanceOf[BoundedCounterContainerExt].__x,
      //          BoundedCounter(
      //            @DropVCs res._2.asInstanceOf[BoundedCounterContainerExt].boundedCounter.counter,
      //            @DropVCs thiss.asInstanceOf[BoundedCounterContainerExt].boundedCounter.bound))
      //     } else {
      //       thiss
      //     }).asInstanceOf[BoundedCounterContainer]
      //     res._1
      //   }, thiss)
      //
      // Note that we are constructing a new BoundedCounter with `res._2.counter` and this.boundedCounter.bound.
      // Since `bcTryAdd` is opaque, the solver does not know the relationship between `res._2.counter` and `this.boundedCounter.bound`.
      // So without further constraints, this will result in an invalid VC.
      // However we know that calling `tryAdd` (which in turns calls `bcTryAdd`) leads to a valid `BoundedCounter`,
      // and that this.boundedCounter.bound is equal to res._2.boundedCounter.bound, therefore making this VC valid by construction
      // We therefore must annotate it with @DropVCs
      tryAdd(i)
    }
  }
}