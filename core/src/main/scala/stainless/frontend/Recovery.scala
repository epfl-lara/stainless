package stainless
package frontend

import utils.StringUtils
import extraction.xlang.{trees => xt}

object DebugSectionRecovery extends inox.DebugSection("recovery")

/** The result of the recovery process, either:
  *
  * - [[RecoveryResult.Success]] with the newly recovered symbols
  * - [[RecoveryResult.Failure]] with a list of irrecoverable definitions and their associated missing dependencies
  */
sealed abstract class RecoveryResult
object RecoveryResult {
  final case class Success(symbols: xt.Symbols) extends RecoveryResult
  final case class Failure(failures: Seq[(xt.Definition, Set[Identifier])]) extends RecoveryResult
}

/** Attempts to use various strategies to recover valid symbols in the presence of missing dependencies */
class Recovery(symbols: xt.Symbols)(using val context: inox.Context) {
  import context.reporter
  private given givenDebugSection: DebugSectionRecovery.type = DebugSectionRecovery
  private given givenPrinterOptions: xt.PrinterOptions = xt.PrinterOptions.fromContext(context)

  import RecoveryResult._

  private val strategies: Seq[RecoveryStrategy] = Seq(
    RecoverExternTypes
  )

  private val strategy = strategies.reduceLeft(_ orElse _)

  def recover(missings: Map[Identifier, Set[Identifier]]): RecoveryResult = {
    val definitions = (
      symbols.functions.values ++
      symbols.classes.values ++
      symbols.typeDefs.values
    ).toSeq

    val recovered = definitions map {
      case d if missings contains d.id =>
        reporter.debug(
          s"\nFound definition with missing dependencies: " +
          s"${d.id.asString} -> ${missings(d.id) map (_.asString) mkString ", "}\n" +
          s" - Attempting recovery..."
        )

        strategy.recover(d, missings(d.id)) match {
          case Left(errs) =>
            reporter.debug(" => FAIL")
            Left(errs)

          case Right(result) =>
            reporter.debug(" => SUCCESS")
            reporter.debug(" > Original:")
            reporter.debug(StringUtils.indent(d.asString, 4))
            reporter.debug("")
            reporter.debug(" > Recovered:")
            reporter.debug(StringUtils.indent(result.asString, 4))
            reporter.debug("")
            Right(result)
        }

      case d => Right(d)
    }

    val (errors, defs) = recovered partition (_.isLeft)
    if (errors.nonEmpty) {
      Failure(errors collect { case Left(err) => err })
    } else {
      val classes = defs collect { case Right(cd: xt.ClassDef) => cd }
      val functions = defs collect { case Right(fd: xt.FunDef) => fd }
      val typeDefs = defs collect { case Right(td: xt.TypeDef) => td }

      Success(xt.NoSymbols.withClasses(classes).withFunctions(functions).withTypeDefs(typeDefs))
    }
  }
}

object Recovery {
  def recover(symbols: xt.Symbols)(using ctx: inox.Context): xt.Symbols = {
    val allDefs = (
      symbols.functions.values ++
      symbols.classes.values ++
      symbols.typeDefs.values
    ).toSeq

    val missings = allDefs.toSeq.flatMap { defn =>
      val missingDeps = findMissingDeps(defn, symbols)
      if (missingDeps.isEmpty) None
      else Some(defn.id -> missingDeps)
    }.toMap

    if (missings.isEmpty) {
      symbols
    } else {
      val recovery = new Recovery(symbols)
      val recovered = recovery.recover(missings) match {
        case RecoveryResult.Success(recovered) =>
          recovered

        case RecoveryResult.Failure(errors) =>
          errors foreach { case (definition, unknowns) =>
            ctx.reporter.error(
              s"${definition.id.uniqueName} depends on missing dependencies: " +
              s"${unknowns map (_.uniqueName) mkString ", "}."
            )
          }
          ctx.reporter.fatalError(s"Cannot recover from missing dependencies")
      }

      symbols ++ recovered
    }
  }

  private def findMissingDeps(defn: xt.Definition, symbols: xt.Symbols): Set[Identifier] = {
    val finder = new utils.XLangDependenciesFinder
    val deps = finder(defn)
    deps.filter { dep =>
      !symbols.classes.contains(dep) &&
      !symbols.functions.contains(dep) &&
      !symbols.typeDefs.contains(dep)
    }
  }
}

/** A strategy to recover a definition with missing dependencies */
abstract class RecoveryStrategy { self =>
  type Recovered[Def] = Either[(Def, Set[Identifier]), Def]

  protected def recoverFunction(fd: xt.FunDef, missing: Set[Identifier]): Recovered[xt.FunDef]
  protected def recoverClass(cd: xt.ClassDef, missing: Set[Identifier]): Recovered[xt.ClassDef]
  protected def recoverTypeDef(td: xt.TypeDef, missing: Set[Identifier]): Recovered[xt.TypeDef]

  def recover[Def <: xt.Definition](definition: Def, missing: Set[Identifier]): Recovered[Def] = {
    definition match {
      case fd: xt.FunDef   => recoverFunction(fd, missing).asInstanceOf[Recovered[Def]]
      case cd: xt.ClassDef => recoverClass(cd, missing).asInstanceOf[Recovered[Def]]
      case td: xt.TypeDef  => recoverTypeDef(td, missing).asInstanceOf[Recovered[Def]]
      case as: xt.ADTSort  => sys.error("There should never be any ADTSort at this stage")
    }
  }

  def orElse(other: RecoveryStrategy): RecoveryStrategy = new RecoveryStrategy {
    override def recover[Def <: xt.Definition](definition: Def, missing: Set[Identifier]): Recovered[Def] = {
      // Note: This begs for some kind of Validation Monad + Semigroup for the error
      self.recover(definition, missing) match {
        case Right(result) => Right(result)
        case Left((selfRes, selfErrs)) => other.recover(selfRes, missing) match {
          case Right(result) => Right(result)
          case Left((otherRes, otherErrs)) => Left((otherRes, selfErrs ++ otherErrs))
        }
      }
    }

    override protected def recoverFunction(fd: xt.FunDef, missing: Set[Identifier]): Recovered[xt.FunDef] =
      recover(fd, missing)

    override protected def recoverClass(cd: xt.ClassDef, missing: Set[Identifier]): Recovered[xt.ClassDef] =
      recover(cd, missing)

    override protected def recoverTypeDef(td: xt.TypeDef, missing: Set[Identifier]): Recovered[xt.TypeDef] =
      recover(td, missing)
  }
}

/** Do not attempt any recovery */
object NoRecovery extends RecoveryStrategy {
  override protected def recoverFunction(fd: xt.FunDef, missing: Set[Identifier]): Recovered[xt.FunDef] =
    Left(fd -> missing)

  override protected def recoverClass(cd: xt.ClassDef, missing: Set[Identifier]): Recovered[xt.ClassDef] =
    Left(cd -> missing)

  override protected def recoverTypeDef(td: xt.TypeDef, missing: Set[Identifier]): Recovered[xt.TypeDef] =
    Left(td -> missing)
}

/** References to unknown class types in `extern` definitions are mapped to BigInt */
object RecoverExternTypes extends RecoveryStrategy {

  private case class ExternType(tpe: xt.Type, isPure: Boolean) {
    def collect(missing: Set[Identifier]): Set[ExternType] = {
      collectMissingTypes(tpe, missing).map(ExternType(_, isPure))
    }
  }

  private object ExternType {
    def apply(vd: xt.ValDef): ExternType = ExternType(vd.tpe, vd.flags contains xt.IsPure)
    def apply(td: xt.TypeDef): ExternType = ExternType(td.rhs, td.flags contains xt.IsPure)
  }

  override protected def recoverFunction(fd: xt.FunDef, missing: Set[Identifier]): Recovered[xt.FunDef] = {
    if (!fd.flags.contains(xt.Extern))
      return Left(fd -> missing)

    val externTypes = fd.params.map(ExternType(_)) ++ Seq(ExternType(fd.returnType, fd.flags contains xt.IsPure))
    val missingTypes = externTypes flatMap (_.collect(missing))
    val subst: Map[xt.Type, xt.Type] = missingTypes.map {
      case ExternType(tp, isPure) => tp -> replaceMissingType(tp, isPure)
    }.toMap

    val returnType = xt.typeOps.replace(subst, fd.returnType)

    Right(fd.copy(
      params = fd.params.map(vd => vd.copy(tpe = xt.typeOps.replace(subst, vd.tpe))),
      returnType = returnType,
      fullBody = xt.NoTree(returnType)
    ))
  }

  override protected def recoverClass(cd: xt.ClassDef, missing: Set[Identifier]): Recovered[xt.ClassDef] = {
    val (externFields, otherFields) = cd.fields.partition(_.flags contains xt.Extern)
    val (externTypes, otherTypes) = (externFields.map(ExternType(_)), otherFields.map(_.tpe))

     val missingExternTypes = externTypes flatMap (_.collect(missing))
     val subst: Map[xt.Type, xt.Type] = missingExternTypes.map {
       case ExternType(tp, isPure) => tp -> replaceMissingType(tp, isPure)
     }.toMap

    val recovered = cd.copy(
      fields = cd.fields.map(vd => vd.copy(tpe = xt.typeOps.replace(subst, vd.tpe)))
    )

    val stillMissing = otherTypes.flatMap(collectMissingTypes(_, missing)).toSet

    if (stillMissing.isEmpty) Right(recovered)
    else Left(recovered -> stillMissing.map(_.id))
  }

  override protected def recoverTypeDef(td: xt.TypeDef, missing: Set[Identifier]): Recovered[xt.TypeDef] = {
    if (!td.flags.contains(xt.Extern))
      return Left(td -> missing)

     val missingExternTypes = ExternType(td).collect(missing)
     val subst: Map[xt.Type, xt.Type] = missingExternTypes.map {
       case ExternType(tp, isPure) => tp -> replaceMissingType(tp, isPure)
     }.toMap

    val recovered = td.copy(rhs = xt.typeOps.replace(subst, td.rhs))
    Right(recovered)
  }

  private def collectMissingTypes(tpe: xt.Type, missing: Set[Identifier]): Set[xt.ClassType] = {
    xt.typeOps.collect[xt.ClassType] {
      case ct @ xt.ClassType(id, _) if missing contains id => Set(ct)
      case _ => Set.empty
    } (tpe)
  }

  private def replaceMissingType(tpe: xt.Type, isPure: Boolean): xt.Type = {
    xt.UnknownType(isPure).copiedFrom(tpe)
  }
}
