package stainless
package verification

trait CoqEncoder {
  implicit val debugSection = DebugSectionCoq

  val p: StainlessProgram
  val ctx: inox.Context
  val st = stainless.trees

  // transform a Stainless expression into a Coq expression
  def transformTree(t: st.Expr): CoqExpression = t match {
    case _ => ctx.reporter.fatalError("The translation to Coq does not support ${t.class} yet.")
  }

  // creates a case for an inductive type
  def makeCase(root: Identifier, a: st.ADTDefinition) = a match { 
    case a: st.ADTConstructor =>
      val fieldsTypes = a.fields.map(vd => vd.tpe match {
        // FIXME: also check for recursive calls to other constructors
        case b: st.ADTType if a.id == b.id || root == b.id => // field using the type of `a` recursively
          ArbitraryExpression(b.id.name)
        case _ => transformType(vd.tpe)
      })
      val arrowType = fieldsTypes.foldLeft[CoqExpression](ArbitraryExpression(root.name))
        { case (acc,field) => Arrow(field,acc)}
      InductiveCase(a.id, arrowType)
    case _ =>
      ctx.reporter.fatalError(s"The translation to Coq does not support $a as a constructor.")
  }

  // transforms an ADT into an inductive type
  def transformADT(a: st.ADTDefinition): CoqCommand = {
    if (a.root(p.symbols) != a) {
      ctx.reporter.debug(s"Skipping $a, since it is not the root of the ADT.")
      NoCommand
    } else {
      a match {
        case a: st.ADTSort =>
          InductiveDefinition(
            a.id,
            a.tparams.map { case p => (p.id, ArbitraryExpression("Type")) },
            a.cons.map(id => makeCase(a.id, p.symbols.adts(id)))
          )
        case _ =>
          ctx.reporter.fatalError(s"The translation to Coq does not support the ADT $a.")
      }
    }
  }

  def transformFunction(fd: st.FunDef): CoqCommand = {
    NoCommand
    // ctx.reporter.fatalError("The translation to Coq does not support Functions yet.")
  }

  // translate a Stainless type to a Coq type
  def transformType(tpe: st.Type): CoqExpression = tpe match {
    case _ => ctx.reporter.fatalError(s"The translation to Coq does not support the type $tpe.")
  }

  def transform(): CoqCommand = {
    Sequence(
      p.symbols.adts.foldLeft[CoqCommand] (NoCommand) { case (acc,(_,adt)) => Sequence(acc,transformADT(adt)) },
      p.symbols.functions.foldLeft[CoqCommand] (NoCommand) { case (acc,(_,fd)) => Sequence(acc,transformFunction(fd)) }
    )
  }
}

object CoqEncoder {
  def transformProgram(program: StainlessProgram, context: inox.Context) = {
    object encoder extends CoqEncoder {
      val p = program
      val ctx = context
    }

    encoder.transform()
  }
}