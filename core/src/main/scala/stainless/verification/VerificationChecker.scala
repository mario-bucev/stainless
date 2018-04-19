/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import inox.Options
import inox.solvers._

import scala.util.{ Success, Failure }
import scala.concurrent.Future
import scala.collection.mutable

object optFailEarly extends inox.FlagOptionDef("fail-early", false)
object optFailInvalid extends inox.FlagOptionDef("fail-invalid", false)
object optVCCache extends inox.FlagOptionDef("vc-cache", true)

object DebugSectionVerification extends inox.DebugSection("verification")

trait VerificationChecker { self =>
  val program: Program
  val context: inox.Context
  val semantics: program.Semantics

  import context._
  import program._
  import program.trees._
  import program.symbols._

  private lazy val failEarly = options.findOptionOrDefault(optFailEarly)
  private lazy val failInvalid = options.findOptionOrDefault(optFailInvalid)
  private lazy val checkModels = options.findOptionOrDefault(optCheckModels)

  implicit val debugSection = DebugSectionVerification

  type VC = verification.VC[program.trees.type]
  val VC = verification.VC

  type VCStatus = verification.VCStatus[program.Model]

  type VCResult = verification.VCResult[program.Model]
  val VCResult = verification.VCResult

  type TimeoutSolverFactory = SolverFactory {
    val program: self.program.type
    type S <: inox.solvers.combinators.TimeoutSolver { val program: self.program.type }
  }

  lazy val evaluator = semantics.getEvaluator(context)

  protected def createFactory(opts: Options): TimeoutSolverFactory

  protected val factoryCache: mutable.Map[Options, TimeoutSolverFactory] = mutable.Map()
  protected def getFactory(opts: inox.Options = options): TimeoutSolverFactory = {
    factoryCache.getOrElseUpdate(opts, opts.findOption(inox.optTimeout) match {
      case Some(to) => createFactory(opts).withTimeout(to)
      case None => createFactory(opts)
    })
  }

  /** @see [[checkAdtInvariantModel]] */
  protected def getFactoryForVC(vc: VC): TimeoutSolverFactory = vc.kind match {
    case _: VCKind.AdtInvariant => getFactory(Options(Seq(optCheckModels(false))))
    case _ => getFactory()
  }

  protected def defaultStop(res: VCResult): Boolean = {
    if (failEarly) !res.isValid
    else if (failInvalid) res.isInvalid
    else false
  }

  def verify(vcs: Seq[VC], stopWhen: VCResult => Boolean = defaultStop): Future[Map[VC, VCResult]] = {
    try {
      reporter.debug("Checking Verification Conditions...")
      checkVCs(vcs, stopWhen)
    } finally {
      factoryCache.values.foreach(_.shutdown())
    }
  }

  private lazy val unknownResult: VCResult = VCResult(VCStatus.Unknown, None, None)

  def checkVCs(vcs: Seq[VC], stopWhen: VCResult => Boolean = defaultStop): Future[Map[VC, VCResult]] = {
    @volatile var stop = false

    val initMap: Map[VC, VCResult] = vcs.map(vc => vc -> unknownResult).toMap

    import MainHelpers._
    val results = Future.traverse(vcs)(vc => Future {
      if (stop) None else {
        val sf = getFactoryForVC(vc)
        val res = checkVC(vc, sf)

        val shouldStop = stopWhen(res)
        interruptManager.synchronized { // Make sure that we only interrupt the manager once.
          if (shouldStop && !stop && !interruptManager.isInterrupted) {
            stop = true
            interruptManager.interrupt()
          }
        }

        if (interruptManager.isInterrupted) interruptManager.reset()
        Some(vc -> res)
      }
    }).map(_.flatten)

    results.map(initMap ++ _)
  }

  /** Check whether the model for the ADT invariant specified by the given (invalid) VC is
   *  valid, ie. whether evalutating the invariant with the given model actually returns `false`.
   *
   *  One needs to be careful, because simply evaluating the invariant over the model
   *  returned by Inox fails with a 'adt invariant' violation. While this is expected,
   *  we cannot know whether it was the invariant that we are interested in at this point
   *  or some other invariant that failed.
   *
   *  Instead, we need to put the constructed ADT value in the model when evaluating the
   *  condition, in order for the evaluator to not attempt to re-construct it.
   *
   *  As such, we instead need to:
   *  - evaluate the ADT's arguments to figure out whether those are valid.
   *  - rebuild the ADT over its evaluated arguments, and add it to the model under a fresh name.
   *  - rewrite the invariant's invocation to be applied to this new variable instead.
   *  - evaluate the resulting condition under the new model.
   */
  protected def checkAdtInvariantModel(vc: VC, invId: Identifier, model: Model): VCStatus = {
    import inox.evaluators.EvaluationResults._

    val evaledModelVars = model.vars.mapValues(v => evaluator.eval(v))
    val failed = evaledModelVars.values.find(_.result.isEmpty)
    failed foreach {
      case RuntimeError(msg) =>
        reporter.warning(s"- Argument to ADT constructor leads to runtime error: $msg")
      case EvaluatorError(msg) =>
        reporter.warning(s"- Argument to ADT constructor leads to evaluation error: $msg")
      case _ =>
        reporter.internalError(s"Expected evaluation of argument to have failed")
    }

    if (failed.isDefined) return VCStatus.Unknown

    val invs = exprOps.collect[FunctionInvocation] {
      case fi: FunctionInvocation if fi.id == invId => Set(fi)
      case _ => Set()
    } (vc.condition)

    val inv @ FunctionInvocation(`invId`, invTps, Seq(adt @ ADT(adtId, tps, args))) = invs.head

    val evaledArgs = evaledModelVars.mapValues(_.result.get)
    val newArgs = args map (arg => exprOps.replaceFromSymbols(evaledArgs, arg))

    val newAdt = ADT(adtId, tps, newArgs)

    val adtVar = Variable(FreshIdentifier("adt"), adt.getType(symbols), Seq())
    val newInv = FunctionInvocation(invId, invTps, Seq(adtVar))
    val newModel = inox.Model(program, context)(model.vars + (adtVar.toVal -> newAdt), model.chooses)
    val newCondition = exprOps.replace(Map(inv -> newInv), vc.condition)

    evaluator.eval(newCondition, newModel) match {
      case Successful(BooleanLiteral(false)) =>
        reporter.debug("- Model validated.")
        VCStatus.Invalid(VCStatus.CounterExample(model))

      case Successful(_) =>
        reporter.debug("- Invalid model.")
        VCStatus.Unknown

      case RuntimeError(msg) =>
        reporter.warning(s"- Model leads to runtime error: $msg")
        VCStatus.Unknown

      case EvaluatorError(msg) =>
        reporter.warning(s"- Model leads to evaluation error: $msg")
        VCStatus.Unknown
    }
  }

  protected def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }): VCResult = {
    import SolverResponses._
    val s = sf.getNewSolver

    try {
      val cond = simplifyLets(vc.condition)
      reporter.synchronized {
        reporter.info(s" - Now solving '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")
        reporter.debug(cond.asString)
        reporter.debug("Solving with: " + s.name)
      }

      val (time, tryRes) = timers.verification.runAndGetTime {
        if (vc.satisfiability) {
          s.assertCnstr(cond)
          s.check(Simple)
        } else {
          s.assertCnstr(Not(cond))
          s.check(Model)
        }
      }

      val vcres = tryRes match {
        case _ if interruptManager.isInterrupted =>
          VCResult(VCStatus.Cancelled, Some(s), Some(time))

        case Success(res) => res match {
          case Unknown =>
            VCResult(s match {
              case ts: inox.solvers.combinators.TimeoutSolver => ts.optTimeout match {
                case Some(t) if t < time => VCStatus.Timeout
                case _ => VCStatus.Unknown
              }
              case _ => VCStatus.Unknown
            }, Some(s), Some(time))

          case Unsat if !vc.satisfiability =>
            VCResult(VCStatus.Valid, s.getResultSolver, Some(time))

          case SatWithModel(model) if checkModels && vc.kind.isInstanceOf[VCKind.AdtInvariant] =>
            val VCKind.AdtInvariant(invId) = vc.kind
            val status = checkAdtInvariantModel(vc, invId, model)
            VCResult(status, s.getResultSolver, Some(time))

          case SatWithModel(model) if !vc.satisfiability =>
            VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), s.getResultSolver, Some(time))

          case Sat if vc.satisfiability =>
            VCResult(VCStatus.Valid, s.getResultSolver, Some(time))

          case Unsat if vc.satisfiability =>
            VCResult(VCStatus.Invalid(VCStatus.Unsatisfiable), s.getResultSolver, Some(time))
        }

        case Failure(u: Unsupported) =>
          reporter.warning(u.getMessage)
          VCResult(VCStatus.Unsupported, Some(s), Some(time))

        case Failure(e) => reporter.internalError(e)
      }

      reporter.synchronized {
        reporter.info(s" - Result for '${vc.kind}' VC for ${vc.fd} @${vc.getPos}:")

        vcres.status match {
          case VCStatus.Valid =>
            reporter.info(" => VALID")

          case VCStatus.Invalid(reason) =>
            reporter.warning(" => INVALID")
            reason match {
              case VCStatus.CounterExample(cex) =>
                reporter.warning("Found counter-example:")
                reporter.warning("  " + cex.asString.replaceAll("\n", "\n  "))

              case VCStatus.Unsatisfiable =>
                reporter.warning("Property wasn't satisfiable")
            }

          case status =>
            reporter.warning(" => " + status.name.toUpperCase)
        }
      }

      vcres
    } finally {
      s.free()
    }
  }
}

object VerificationChecker {
  def verify(p: StainlessProgram, ctx: inox.Context)
            (vcs: Seq[VC[p.trees.type]]): Future[Map[VC[p.trees.type], VCResult[p.Model]]] = {
    class Checker extends VerificationChecker {
      val program: p.type = p
      val context = ctx
      val semantics = program.getSemantics

      protected def createFactory(opts: Options) = solvers.SolverFactory(p, ctx.withOpts(opts.options: _*))
    }

    val checker = if (ctx.options.findOptionOrDefault(optVCCache)) {
      new Checker with VerificationCache
    } else {
      new Checker
    }

    checker.verify(vcs)
  }
}
