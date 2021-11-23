package stainless
package frontend

import utils.{Caches, ExtractionCache, StringUtils, XLangSerializer}
import extraction.xlang.{trees => xt}
import stainless.ast

import scala.collection.mutable
import java.io.{DataInputStream, File, FileInputStream}
import scala.util.control.NonFatal

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

  import RecoveryStrategy._
  import RecoveryResult._

  private val strategies: Seq[RecoveryStrategy] =
    Seq(RecoverExternTypes) /*++
      (if (context.options.findOptionOrDefault(ExtractionCache.optIncrementalCompilation))
        Seq(new RecoverExtractedSymbols)
      else Seq.empty)*/

  private val strategy = strategies.reduceLeft(_ orElse _).fixpoint

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
          case PartiallyRecovered(_, _, stillMissing) =>
            reporter.debug(" => FAIL")
            Left((d, stillMissing))

          case Recovered(result, recoveredDefs) =>
            reporter.debug(" => SUCCESS")
            reporter.debug(" > Original:")
            reporter.debug(StringUtils.indent(d.asString, 4))
            reporter.debug("")
            reporter.debug(" > Recovered:")
            reporter.debug(StringUtils.indent(result.asString, 4))
            reporter.debug("")
            Right((result, recoveredDefs))
        }

      case d => Right((d, Map.empty[Identifier, xt.Definition]))
    }

    val (errors, defs) = recovered partitionMap identity
    if (errors.nonEmpty) {
      Failure(errors)
    } else {
      val (classess, functionss, typeDefss) = defs.map {
        case (updatedDef, recoveredDefs) =>
          val defs = recoveredDefs.values.toSeq :+ updatedDef
          val classes = defs.collect { case cd: xt.ClassDef => cd }
          val functions = defs.collect { case fd: xt.FunDef => fd }
          val typeDefs = defs.collect { case td: xt.TypeDef => td }
          (classes, functions, typeDefs)
      }.unzip3

      Success(xt.NoSymbols.withClasses(classess.flatten).withFunctions(functionss.flatten).withTypeDefs(typeDefss.flatten))
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

    val missings = allDefs.flatMap { defn =>
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
  import RecoveryStrategy._

  protected def recoverFunction(fd: xt.FunDef, missing: Set[Identifier]): DefinitionRecovery[xt.FunDef]
  protected def recoverClass(cd: xt.ClassDef, missing: Set[Identifier]): DefinitionRecovery[xt.ClassDef]
  protected def recoverTypeDef(td: xt.TypeDef, missing: Set[Identifier]): DefinitionRecovery[xt.TypeDef]

  def recover[Def <: xt.Definition](definition: Def, missing: Set[Identifier]): DefinitionRecovery[Def] = {
    definition match {
      case fd: xt.FunDef   => recoverFunction(fd, missing).asInstanceOf[DefinitionRecovery[Def]]
      case cd: xt.ClassDef => recoverClass(cd, missing).asInstanceOf[DefinitionRecovery[Def]]
      case td: xt.TypeDef  => recoverTypeDef(td, missing).asInstanceOf[DefinitionRecovery[Def]]
      case _: xt.ADTSort  => sys.error("There should never be any ADTSort at this stage")
    }
  }

  // TODO: orElse is misnamed because the partial result from "self" is fed into "other.recover" in case of failure
  final def orElse(other: RecoveryStrategy): RecoveryStrategy = new RecoveryStrategy {
    override def recover[Def <: xt.Definition](definition: Def, missing: Set[Identifier]): DefinitionRecovery[Def] = {
      // Note: This begs for some kind of Validation Monad + Semigroup for the error
      self.recover(definition, missing) match {
        case r@Recovered(_, _) => r
        case PartiallyRecovered(updatedDef, recovered, stillMissing) => other.recover(updatedDef, stillMissing) match {
          case r@Recovered(_, _) => r
          case pr@PartiallyRecovered(_, _, _) => pr.withAddedRecovered(recovered)
        }
      }
    }

    override protected def recoverFunction(fd: xt.FunDef, missing: Set[Identifier]): DefinitionRecovery[xt.FunDef] =
      recover(fd, missing)

    override protected def recoverClass(cd: xt.ClassDef, missing: Set[Identifier]): DefinitionRecovery[xt.ClassDef] =
      recover(cd, missing)

    override protected def recoverTypeDef(td: xt.TypeDef, missing: Set[Identifier]): DefinitionRecovery[xt.TypeDef] =
      recover(td, missing)
  }

  final def fixpoint: RecoveryStrategy = new RecoveryStrategy {
    override def recover[Def <: xt.Definition](definition: Def, missing: Set[Identifier]): DefinitionRecovery[Def] =
      inox.utils.fixpoint[DefinitionRecovery[Def]] {
        case r@Recovered(_, _) => r
        case PartiallyRecovered(updatedDef, recovered, stillMissing) =>
          self.recover(updatedDef, stillMissing).withAddedRecovered(recovered)
      }(PartiallyRecovered(definition, Map.empty, missing))

    override protected def recoverFunction(fd: xt.FunDef, missing: Set[Identifier]): DefinitionRecovery[xt.FunDef] =
      recover(fd, missing)

    override protected def recoverClass(cd: xt.ClassDef, missing: Set[Identifier]): DefinitionRecovery[xt.ClassDef] =
      recover(cd, missing)

    override protected def recoverTypeDef(td: xt.TypeDef, missing: Set[Identifier]): DefinitionRecovery[xt.TypeDef] =
      recover(td, missing)
  }
}

object RecoveryStrategy {
  sealed trait DefinitionRecovery[Def] {
    val updatedDef: Def
    val recovered: Map[Identifier, xt.Definition]
    def withAddedRecovered(r: Map[Identifier, xt.Definition]): DefinitionRecovery[Def] =
      this match {
        case Recovered(newDef, recovered) => Recovered(newDef, recovered ++ r)
        case PartiallyRecovered(newDef, recovered, stillMissing) => PartiallyRecovered(newDef, recovered ++ r, stillMissing)
      }
  }
  case class Recovered[Def](updatedDef: Def, recovered: Map[Identifier, xt.Definition]) extends DefinitionRecovery[Def]
  // Partially recovered, or not at all.
  case class PartiallyRecovered[Def](updatedDef: Def, recovered: Map[Identifier, xt.Definition], stillMissing: Set[Identifier]) extends DefinitionRecovery[Def] {
    require(stillMissing.nonEmpty)
  }
}

/** Do not attempt any recovery */
object NoRecovery extends RecoveryStrategy {
  import RecoveryStrategy._

  override protected def recoverFunction(fd: xt.FunDef, missing: Set[Identifier]): DefinitionRecovery[xt.FunDef] =
    PartiallyRecovered(fd, Map.empty, missing)

  override protected def recoverClass(cd: xt.ClassDef, missing: Set[Identifier]): DefinitionRecovery[xt.ClassDef] =
    PartiallyRecovered(cd, Map.empty, missing)

  override protected def recoverTypeDef(td: xt.TypeDef, missing: Set[Identifier]): DefinitionRecovery[xt.TypeDef] =
    PartiallyRecovered(td, Map.empty, missing)
}

/** References to unknown class types in `extern` definitions are mapped to BigInt */
object RecoverExternTypes extends RecoveryStrategy {
  import RecoveryStrategy._

  private case class ExternType(tpe: xt.Type, isPure: Boolean) {
    def collect(missing: Set[Identifier]): Set[ExternType] = {
      collectMissingTypes(tpe, missing).map(ExternType(_, isPure))
    }
  }

  private object ExternType {
    def apply(vd: xt.ValDef): ExternType = ExternType(vd.tpe, vd.flags contains xt.IsPure)
    def apply(td: xt.TypeDef): ExternType = ExternType(td.rhs, td.flags contains xt.IsPure)
  }

  override protected def recoverFunction(fd: xt.FunDef, missing: Set[Identifier]): DefinitionRecovery[xt.FunDef] = {
    if (!fd.flags.contains(xt.Extern))
      return PartiallyRecovered(fd, Map.empty, missing)

    val externTypes = fd.params.map(ExternType(_)) ++ Seq(ExternType(fd.returnType, fd.flags contains xt.IsPure))
    val missingTypes = externTypes flatMap (_.collect(missing))
    val subst: Map[xt.Type, xt.Type] = missingTypes.map {
      case ExternType(tp, isPure) => tp -> replaceMissingType(tp, isPure)
    }.toMap

    val returnType = xt.typeOps.replace(subst, fd.returnType)

    Recovered(fd.copy(
      params = fd.params.map(vd => vd.copy(tpe = xt.typeOps.replace(subst, vd.tpe))),
      returnType = returnType,
      fullBody = xt.NoTree(returnType)
    ), Map.empty)
  }

  override protected def recoverClass(cd: xt.ClassDef, missing: Set[Identifier]): DefinitionRecovery[xt.ClassDef] = {
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

    if (stillMissing.isEmpty) Recovered(recovered, Map.empty)
    else PartiallyRecovered(recovered, Map.empty, stillMissing.map(_.id))
  }

  override protected def recoverTypeDef(td: xt.TypeDef, missing: Set[Identifier]): DefinitionRecovery[xt.TypeDef] = {
    if (!td.flags.contains(xt.Extern))
      return PartiallyRecovered(td, Map.empty, missing)

     val missingExternTypes = ExternType(td).collect(missing)
     val subst: Map[xt.Type, xt.Type] = missingExternTypes.map {
       case ExternType(tp, isPure) => tp -> replaceMissingType(tp, isPure)
     }.toMap

    val recovered = td.copy(rhs = xt.typeOps.replace(subst, td.rhs))
    Recovered(recovered, Map.empty)
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
/*
class RecoverExtractedSymbols(using context: inox.Context) extends RecoveryStrategy {
  import RecoveryStrategy._
  import ast.SymbolIdentifier

  private val (allDefs, allDefsSyms): (Map[(String, String), (SymbolIdentifier, xt.Definition)], xt.Symbols) = {
    val (cds, fds, tds) = ExtractionCache.readAllExtracted
    val freshener = new SymbolFreshener
    val newCds = cds.map(freshener.transform)
    val newFds = fds.map(freshener.transform)
    val newTds = tds.map(freshener.transform)
    // Applying the same set of transformation as in Preprocessing
    val syms = {
      val syms = xt.NoSymbols.withClasses(newCds).withFunctions(newFds).withTypeDefs(newTds)
      frontend.strictBVCleaner.transform(utils.LibraryFilter.removeLibraryFlag(syms))
    }
    val mapping = (syms.classes ++ syms.functions ++ syms.typeDefs).flatMap {
      case (si: SymbolIdentifier, d) =>
        Some((si.name, si.symbol.name) -> (si, d))
      case _ => None
    }.toMap
    (mapping, syms)
  }

  override def recover[Def <: xt.Definition](definition: Def, missing: Set[Identifier]): DefinitionRecovery[Def] = {
    val found: Map[SymbolIdentifier, (SymbolIdentifier, xt.Definition)] = missing.flatMap {
      case missng: SymbolIdentifier => allDefs.get((missng.name, missng.symbol.name)).map(d => (missng, d))
      case _ => None
    }.toMap
    val stillMissing = missing -- found.keys

    val symMapper = new SymbolTransformer {
      override def substitute(si: SymbolIdentifier): Option[SymbolIdentifier] =
        found.get(si).map(_._1)
    }
    val newDef = symMapper.transformDef(definition).asInstanceOf[Def]

    val deps = found.values.flatMap((s, _) => allDefsSyms.dependencies(s))
    val recovered =
      found.values.map((s, d) => (s: Identifier) -> d).toMap ++
        deps.flatMap {
          case dep: SymbolIdentifier => allDefs.get((dep.name, dep.symbol.name)).map((_, d) => (dep: Identifier, d))
          case _ => None
        }.toMap

    if (stillMissing.isEmpty) Recovered(newDef, recovered)
    else PartiallyRecovered(newDef, recovered, stillMissing)
  }

  override protected def recoverFunction(fd: xt.FunDef, missing: Set[Identifier]): DefinitionRecovery[xt.FunDef] =
    recover(fd, missing)

  override protected def recoverClass(cd: xt.ClassDef, missing: Set[Identifier]): DefinitionRecovery[xt.ClassDef] =
    recover(cd, missing)

  override protected def recoverTypeDef(td: xt.TypeDef, missing: Set[Identifier]): DefinitionRecovery[xt.TypeDef] =
    recover(td, missing)

  private abstract class SymbolTransformer extends xt.ConcreteXLangSelfTreeTransformer {
    def substitute(si: SymbolIdentifier): Option[SymbolIdentifier]

    override def transform(id: Identifier): Identifier = id match {
      case si: SymbolIdentifier => substitute(si).getOrElse(si)
      case _ => id
    }

    override def transform(e: xt.Expr): xt.Expr = e match {
      // We need to explicitly transform LetClass to ensure we go through in each local methods
      // because the deconstructor of LetClass does not deconstruct local methods.
      case xt.LetClass(classes, body) =>
        xt.LetClass(classes.map(transform), transform(body))
      case e =>
        super.transform(e)
    }

    def transformDef(d: xt.Definition): xt.Definition = d match {
      case vd: xt.ValDef => transform(vd)
      case tpd: xt.TypeParameterDef => transform(tpd)
      case fd: xt.FunDef => transform(fd)
      case sort: xt.ADTSort => transform(sort)
      case cd: xt.ClassDef => transform(cd)
      case td: xt.TypeDef => transform(td)
      case lcd: xt.LocalClassDef => transform(lcd)
      case lmd: xt.LocalMethodDef => transform(lmd)
      case ltd: xt.LocalTypeDef => transform(ltd)
      case _ => sys.error(s"Unknown definition type: $d")
    }
  }

  private class SymbolFreshener extends SymbolTransformer {
    // Important: Note that we are not using SymbolIdentifier as keys, because their hash and equal method are
    // based on globalId, which are stale when reading them off the extracted files.
    // For instance, if we compile two files A.scala and B.scala separately (i.e. not in the same compilation run),
    // each of them containing the symbols def a and def b respectively, these methods may get the same global id.
    // If we read their extracted binary file later on, they would be considered "equal" due to their global id
    // being the same (even when they should not).
    // Instead, we are using their identifier name and symbol name.
    private val symIdMapping = mutable.Map.empty[(String, String), SymbolIdentifier]
    // Same story here.
    private val symMapping = mutable.Map.empty[String, ast.Symbol]

    override def substitute(si: SymbolIdentifier): Option[SymbolIdentifier] =
      Some(symIdMapping.getOrElseUpdate((si.name, si.symbol.name), {
        val id = FreshIdentifier(si.name)
        val sym = symMapping.getOrElseUpdate(si.symbol.name, ast.Symbol(si.symbol.name))
        new SymbolIdentifier(id, sym)
      }))
  }
}
*/