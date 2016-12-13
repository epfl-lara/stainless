/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait GlobalStateIntroduction extends inox.ast.SymbolTransformer {
  val s: Trees
  val t: Trees

  def transform(syms: s.Symbols): t.Symbols = {

    val globalStateCCD = new CaseClassDef(FreshIdentifier("GlobalState"), Seq(), None, false)
    val epsilonSeed = FreshIdentifier("epsilonSeed", IntegerType)
    globalStateCCD.setFields(Seq(ValDef(epsilonSeed).setIsVar(true)))

    val fds = allFunDefs(pgm)
    var updatedFunctions: Map[FunDef, FunDef] = Map()
    
    val statefulFunDefs = funDefsNeedingState(pgm)

    /*
     * The first pass will introduce all new function definitions,
     * so that in the next pass we can update function invocations
     */
    for {
      fd <- fds if statefulFunDefs.contains(fd)
    } {
      updatedFunctions += (fd -> extendFunDefWithState(fd, globalStateCCD)(ctx))
    }

    for {
      fd <- fds if statefulFunDefs.contains(fd)
    } {
      updateBody(fd, updatedFunctions, globalStateCCD, epsilonSeed)(ctx)
    }

    val pgm0 = replaceDefsInProgram(pgm)(updatedFunctions)

    val globalStateModule = ModuleDef(FreshIdentifier("GlobalStateModule"), Seq(globalStateCCD), false)
    val globalStateUnit = UnitDef(FreshIdentifier("GlobalStateUnit"), List("leon", "internal"), Seq(), Seq(globalStateModule), false)
    pgm0.copy(units = globalStateUnit :: pgm0.units)
  }

  private def extendFunDefWithState(fd: FunDef, stateCCD: CaseClassDef)(ctx: LeonContext): FunDef = {
    val newParams = fd.params :+ ValDef(FreshIdentifier("globalState", stateCCD.typed))
    val newFunDef = new FunDef(fd.id.freshen, fd.tparams, newParams, fd.returnType)
    newFunDef.addFlags(fd.flags)
    newFunDef.setPos(fd)
    newFunDef
  }

  private def updateBody(fd: FunDef, updatedFunctions: Map[FunDef, FunDef], globalStateCCD: CaseClassDef, epsilonSeed: Identifier)(ctx: LeonContext): FunDef = {
    val nfd = updatedFunctions(fd)
    val stateParam: ValDef = nfd.params.last

    nfd.body = fd.body.map(body => postMap{
      case fi@FunctionInvocation(efd, args) if updatedFunctions.contains(efd.fd) => {
        Some(FunctionInvocation(updatedFunctions(efd.fd).typed(efd.tps), args :+ stateParam.id.toVariable))
      }
      case eps@Epsilon(pred, _) => {
        val nextEpsilonSeed = Plus(
                                CaseClassSelector(globalStateCCD.typed, stateParam.id.toVariable, epsilonSeed),
                                InfiniteIntegerLiteral(1))
        Some(Block(Seq(FieldAssignment(stateParam.id.toVariable, epsilonSeed, nextEpsilonSeed)), eps))
      }
      case _ => None
    }(body))

    nfd.precondition = fd.precondition
    nfd.postcondition = fd.postcondition

    nfd
  }

  def funDefsNeedingState(pgm: Program): Set[FunDef] = {

    def compute(body: Expr): Boolean = exists{ 
      case Epsilon(_, _) => true 
      case _ => false
    }(body)

    def combine(b1: Boolean, b2: Boolean) = b1 || b2

    programFixpoint(pgm, compute, combine).filter(p => p._2).keySet
  }

  /*
   * compute some A for each function in the program, including any nested
   * functions (LetDef). The A value is transitive, combined with the A value
   * of all called functions in the body. The combine function combines the current
   * value computed with a new value from a function invocation.
   */
  private def programFixpoint[A](pgm: Program, compute: (Expr) => A, combine: (A, A) => A): Map[FunDef, A] = {

    //currently computed results (incremental)
    var res: Map[FunDef, A] = Map()
    //missing dependencies for a function
    var missingDependencies: Map[FunDef, Set[FunctionInvocation]] = Map()

    def fullyComputed(fd: FunDef): Boolean = !missingDependencies.isDefinedAt(fd)

    for {
      fd <- allFunDefs(pgm)
    } {
      fd.body match {
        case None =>
          () //TODO: maybe some default value?  res += (fd -> Set())
        case Some(body) => {
          res = res + (fd -> compute(body))
          val missingCalls: Set[FunctionInvocation] = functionCallsOf(body).filterNot(fi => fi.tfd.fd == fd)
          if(missingCalls.nonEmpty)
            missingDependencies += (fd -> missingCalls)
        }
      }
    }

    def rec(): Unit = {
      val previousMissingDependencies = missingDependencies

      for{ (fd, calls) <- missingDependencies } {
        var newMissingCalls: Set[FunctionInvocation] = calls
        for(fi <- calls) {
          val newA = res.get(fi.tfd.fd).map(ra => combine(res(fd), ra)).getOrElse(res(fd))
          res += (fd -> newA)

          if(fullyComputed(fi.tfd.fd)) {
            newMissingCalls -= fi
          }
        }
        if(newMissingCalls.isEmpty)
          missingDependencies = missingDependencies - fd
        else
          missingDependencies += (fd -> newMissingCalls)
      }

      if(missingDependencies != previousMissingDependencies) {
        rec()
      }
    }

    rec()
    res
  }


  /*
   * returns all fun def in the program, including local definitions inside
   * other functions (LetDef).
   */
  private def allFunDefs(pgm: Program): Seq[FunDef] =
      pgm.definedFunctions.flatMap(fd => 
        fd.body.toSet.flatMap((bd: Expr) =>
          nestedFunDefsOf(bd)) + fd)


}
