object i839b:

  object Aggregation:
    def lastValue = new LastValueAggregation

  sealed trait Aggregation:
    def foo = 0

  object LastValueAggregation:
    private val INITIAL_VALUE: Long = 0L

  case class LastValueAggregation(private var lastValue: Long = LastValueAggregation.INITIAL_VALUE)
      extends Aggregation {}
