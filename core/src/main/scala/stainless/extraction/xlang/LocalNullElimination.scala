package stainless
package extraction
package xlang

import stainless.ast

class LocalNullElimination(override val s: Trees)(override val t: s.type)
                          (using override val context: inox.Context)
  extends oo.CachingPhase
    with SimplyCachedFunctions
    with SimpleFunctions
    with IdentitySorts
    with oo.NoSummaryPhase
    with oo.IdentityTypeDefs
    with oo.IdentityClasses { self =>
  import s._

  case class TransformerContext(symbols: Symbols,
                                optionMutDefs: OptionMutDefs,
                                classesNullableSelections: Map[Identifier, NullableSelections],
                                uninitClasses: UninitClassDefs) {
    def allNewClasses: Seq[ClassDef] = optionMutDefs.allNewClasses ++ uninitClasses.allNewClasses
    def allNewFunctions: Seq[FunDef] = optionMutDefs.allNewFunctions ++ uninitClasses.allNewFunctions
  }

  override protected def getContext(symbols: s.Symbols): TransformerContext = {
    given s.Symbols = symbols

    val uninitCC = new UninitClassesCollector
    for ((_, fd) <- symbols.functions) {
      uninitCC.traverse(fd.fullBody, uninitCC.Env.init)
    }

    // println(uninitCC.classesConsInfo)

    val optMutDefs = mkOptionMutDefs()

    // println("---------------")

//    val uninitClasses = createUninitClasses(symbols, optMutDefs, uninitCC.classesNullableSelections)

    /*
    println(uninitClasses.init2cd.mkString("\n"))
    println("===========================================")
    println("===========================================")
    */
//    TransformerContext(symbols, optMutDefs, uninitCC.classesConsInfo, uninitClasses)
    ???
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (t.FunDef, Unit) = {
    val transformer = new Eliminator(context)
    val newBody = transformer.transform(fd.fullBody, transformer.Env(transformer.CtxKind.Pure(), Map.empty))
    (fd.copy(fullBody = newBody), ())
  }

  override protected def extractSymbols(tc: TransformerContext, symbols: s.Symbols): (t.Symbols, OOAllSummaries) = {
    val (exSyms, exSum) = super.extractSymbols(tc, symbols)
    val resSyms = exSyms.withClasses(tc.allNewClasses).withFunctions(tc.allNewFunctions)
    println(resSyms)
    resSyms.ensureWellFormed
    (resSyms, exSum)
  }

  private class Eliminator(tc: TransformerContext) extends inox.transformers.Transformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    val fieldsOfClass: Map[Identifier, Identifier] = {
      tc.symbols.classes.flatMap { case (clsId, cd) =>
        cd.fields.map(_.id -> clsId).toMap
      }
    }

    case class Env(ctxKind: CtxKind, bdgs: Map[Variable, BdgInfo]) {
      def withPureCtx: Env = Env(CtxKind.Pure(), bdgs)
    }
    case class BdgInfo(info: ExprInfo, newTpe: Type)
    enum CtxKind {
      case ConstructionOrBinding(fullyInit: Boolean, nullable: Boolean, expectedType: Type)
      case FieldSelection(fullyInit: Boolean)
      case Pure()

      def fullyInitAndNullable: (Boolean, Boolean) = this match {
        case ConstructionOrBinding(fullyInit, nullable, _) => (fullyInit, nullable)
        case FieldSelection(fullyInit) => (fullyInit, false)
        case Pure() => (true, false)
      }
    }

    // TODO: Expliquer ces tp
    def adaptExpression(e: Expr, eOrigTpe: Type, eNewTpe: Type, eFullyInit: Boolean, eNullable: Boolean,
                        resFullyInit: Boolean, resNullable: Boolean): Expr = {
      if (resFullyInit == !eFullyInit) {
        val e1 = {
          if (eNullable) get(e).copiedFrom(e)
          else e
        }
        val (e2, tpe2) = eOrigTpe match {
          case ClassType(clsId, clsTps) =>
            assert(clsTps.isEmpty)
            val uninitCd = tc.uninitClasses.init2cd(clsId)
            if (!resFullyInit) {
              (FunctionInvocation(uninitCd.fromInitId, Seq.empty, Seq(e1)).copiedFrom(e), ClassType(uninitCd.cd.id, Seq.empty))
            } else {
              (MethodInvocation(e1, uninitCd.toInitId, Seq.empty, Seq.empty).copiedFrom(e), ClassType(clsId, Seq.empty))
            }
          // TODO: What about array of array of uninit or array of something containing uninit???
          case ArrayType(ClassType(clsId, clsTps)) =>
            assert(clsTps.isEmpty)
            val uninitCd = tc.uninitClasses.init2cd(clsId)
            if (!resFullyInit) {
              (FunctionInvocation(uninitCd.fromInitArrId, Seq.empty, Seq(e1)).copiedFrom(e), ArrayType(ClassType(uninitCd.cd.id, Seq.empty)))
            } else {
              (FunctionInvocation(uninitCd.toInitArrId, Seq.empty, Seq(e1)).copiedFrom(e), ArrayType(ClassType(clsId, Seq.empty)))
            }
          case _ => sys.error(s"Expected a class type or an array of class type but got $eOrigTpe")
        }
        if (resNullable) some(e2, tpe2) else e2
      } else {
        if (resNullable == !eNullable) {
          if (!resNullable) get(e).copiedFrom(e)
          else some(e, eNewTpe).copiedFrom(e)
        } else e
      }
    }

    def mustUseUninit(args: Seq[Expr], env: Env): Boolean = {
      val argsInfo = args.map(exprInfoOf(_, env.bdgs.view.mapValues(_.info).toMap))
      val argsFullyInit = argsInfo.forall(_.fullyInit)
      val argsNullable = argsInfo.exists(_.nullable)
      !argsFullyInit || argsNullable
    }

    override def transform(e: Expr, env: Env): Expr = {
      e match {
        case NullLit() =>
          ???
          /*
          env.ctxKind match {
            case CtxKind.ConstructionOrBinding(_, nullable, expectedType) =>
              if (!nullable) throw MalformedStainlessCode(e, "Unsupported usage of `null` (construction or binding)")
              val ClassType(id, tps) = getAsClassType(expectedType)
              assert(id == tc.optionMutDefs.option.id && tps.size == 1)
              none(tps.head).copiedFrom(e)
            case CtxKind.FieldSelection(_) => throw MalformedStainlessCode(e, "Unsupported usage of `null` (field selection)")
            case CtxKind.Pure() => throw MalformedStainlessCode(e, "Unsupported usage of `null` (pure context)")
          }
          */
        case v: Variable =>
          ???
          /*
          val (resFullyInit, resNullable) = env.ctxKind.fullyInitAndNullable
          env.bdgs.get(v) match {
            case Some(BdgInfo(ExprInfo(_, vFullyInit, vNullable), vNewTpe)) =>
              val v2 = v.copy(tpe = vNewTpe)
              adaptExpression(v2, eOrigTpe = v.tpe, eNewTpe = vNewTpe, vFullyInit, vNullable, resFullyInit, resNullable)
            case None =>
              adaptExpression(v, v.tpe, v.tpe, true, false, resFullyInit, resNullable)
          }
          */
        case Let(vd, ee, body) => letCase(vd, ee, body, env)(Let.apply).copiedFrom(e)
        case LetVar(vd, ee, body) => letCase(vd, ee, body, env)(LetVar.apply).copiedFrom(e)

        case FiniteArray(elems, base) =>
          ???
          /*
          val (elemsFullyInit, elemsNullable, newBase) = base match {
            case ct: ClassType =>
              tc.uninitClasses.init2cd.get(ct.id) match {
                case Some(uninitCd) =>
                  val elemsInfo = elems.map(exprInfoOf(_, env.bdgs.view.mapValues(_.info).toMap))
                  val elemsFullyInit = elemsInfo.forall(_.fullyInit)
                  val elemsNullable = elemsInfo.exists(_.nullable)
                  (elemsFullyInit, elemsNullable, ClassType(uninitCd.cd.id, Seq.empty))
                case None => (true, false, base)
              }
            case _ => (true, false, base)
          }
          val recEnv = Env(CtxKind.ConstructionOrBinding(fullyInit = elemsFullyInit, nullable = elemsNullable, expectedType = newBase), env.bdgs)
          val recElems = elems.map(transform(_, recEnv))
          val (resFullyInit, resNullable) = env.ctxKind.fullyInitAndNullable
          adaptExpression(FiniteArray(recElems, newBase), eOrigTpe = ArrayType(base), eNewTpe = ArrayType(newBase), elemsFullyInit, elemsNullable, resFullyInit, resNullable)
          */
        case ArrayUpdate(arr, ix, value) =>
          ???

        case ArrayUpdated(arr, ix, value) =>
          ???

        case ArraySelect(arr, ix) =>
          ???
          /*
          val arrInfo = exprInfoOf(arr, env.bdgs.view.mapValues(_.info).toMap)
          val arrRec = transform(arr, Env(CtxKind.FieldSelection(arrInfo.fullyInit), env.bdgs))
          val ixRec = transform(ix, env.withPureCtx)
          val origTpe = e.getType(using tc.symbols)
          val tpe2 = {
            if (arrInfo.fullyInit) origTpe
            else {
              // TODO: Array of something else than Uninit
              val ClassType(clsId, clsTps) = getAsClassType(origTpe)
              assert(clsTps.isEmpty)
              val uninitCd = tc.uninitClasses.init2cd(clsId).cd
              ClassType(uninitCd.id, Seq.empty)
            }
          }
          val (resFullyInit, resNullable) = env.ctxKind.fullyInitAndNullable
          // TODO: No, there is a difference between being nullable and having the element being nullable!!!!
          adaptExpression(ArraySelect(arrRec, ixRec), eOrigTpe = origTpe, eNewTpe = tpe2, eFullyInit = arrInfo.fullyInit, eNullable = arrInfo.fullyInit, resFullyInit, resNullable)
          */
        case ClassConstructor(ct, args) =>
          ???
          /*
          val fieldsOrig = tc.symbols.getClass(ct.id).fields
          val (argsEnv, useUninit) = tc.uninitClasses.init2cd.get(ct.id) match {
            case Some(uninitCd) =>
              assert(ct.tps.isEmpty)
              val useUninit = mustUseUninit(args, env)
              val fieldsInfo = tc.classesConsInfo(ct.id).fields

              val argsEnv = fieldsOrig.zipWithIndex.map { case (field, fieldIx) =>
                val fieldInfo = fieldsInfo(field.id)
                val ctxKind = CtxKind.ConstructionOrBinding(
                  // TODO: Upd comment
                  // If all argument are fully initialized, then so is this one
                  // However, if there is one uninit argument, this argument is uninit as well if
                  // its corresponding field is uninit, otherwise we proceed to a fully initialized construction
                  !useUninit || fieldInfo.fullyInit,
                  // Ditto for nullable
                  useUninit && fieldInfo.nullable,
                  uninitCd.cd.fields(fieldIx).tpe
                )
                Env(ctxKind, env.bdgs)
              }
              (argsEnv, useUninit)
            case None =>
              val argsEnv = fieldsOrig.map(field => Env(CtxKind.ConstructionOrBinding(fullyInit = true, nullable = false, expectedType = field.tpe), env.bdgs))
              (argsEnv, false)
          }
          val recArgs = args.zip(argsEnv).map(transform(_, _))
          val (e1, tpe1) = {
            if (useUninit) {
              assert(ct.tps.isEmpty)
              val newCt = ClassType(tc.uninitClasses.init2cd(ct.id).cd.id, Seq.empty)
              (ClassConstructor(newCt, recArgs), newCt)
            } else (ClassConstructor(ct, recArgs), ct)
          }
          val (resFullyInit, resNullable) = env.ctxKind.fullyInitAndNullable
          adaptExpression(e1, eOrigTpe = ct, eNewTpe = tpe1, !useUninit, false, resFullyInit, resNullable)
          */
        case ClassSelector(recv, selector) =>
          ???
          /*
          val recvInfo = exprInfoOf(recv, env.bdgs.view.mapValues(_.info).toMap)
          val recvRec = transform(recv, Env(CtxKind.FieldSelection(recvInfo.fullyInit), env.bdgs))
          val clsId = fieldsOfClass(selector)
          val origCd = tc.symbols.getClass(clsId)
          val origTpe = e.getType(using tc.symbols)
          val (e2, tpe2, selNullable, selFullyInit) = {
            if (recvInfo.fullyInit) (ClassSelector(recvRec, selector).copiedFrom(e), origTpe, false, true)
            else {
              assert(origCd.tparams.isEmpty)
              val uninitCd = tc.uninitClasses.init2cd(clsId).cd
              val selIx = origCd.fields.indexWhere(_.id == selector)
              val fieldInfo = tc.classesConsInfo(origCd.id).fields(selector)
              val newSel = uninitCd.fields(selIx)
              (ClassSelector(recvRec, newSel.id).copiedFrom(e), newSel.tpe, fieldInfo.nullable, fieldInfo.fullyInit)
            }
          }
          val (resFullyInit, resNullable) = env.ctxKind.fullyInitAndNullable
          adaptExpression(e2, eOrigTpe = origTpe, eNewTpe = tpe2, selFullyInit, selNullable, resFullyInit, resNullable)
          */
        case Assignment(v, value) =>
          ???
          /*
          assert(env.ctxKind == CtxKind.Pure())
          val (ctxKind, newTpe) = env.bdgs.get(v) match {
            case Some(BdgInfo(ExprInfo(_, fullyInit, nullable), newTpe)) =>
              (CtxKind.ConstructionOrBinding(fullyInit, nullable, v.tpe), newTpe)
            case None => (CtxKind.ConstructionOrBinding(fullyInit = true, nullable = false, v.tpe), v.tpe)
          }
          val valueRec = transform(value, Env(ctxKind, env.bdgs))
          Assignment(v.copy(tpe = newTpe), valueRec).copiedFrom(e)
          */

        case fa @ FieldAssignment(recv, selector, value) =>
          ???
          /*
          assert(env.ctxKind == CtxKind.Pure())
          val recvInfo = exprInfoOf(recv, env.bdgs.view.mapValues(_.info).toMap)
          val recvRec = transform(recv, Env(CtxKind.FieldSelection(recvInfo.fullyInit), env.bdgs))
          val clsId = fieldsOfClass(selector)
          val origCd = tc.symbols.getClass(clsId)
          val selTpe = fa.getField(using tc.symbols).get.tpe
          val (selId, valueCtxKind) = {
            if (recvInfo.fullyInit) {
              // TODO: Test this
              (selector, CtxKind.ConstructionOrBinding(fullyInit = true, nullable = false, expectedType = selTpe))
            } else {
              assert(origCd.tparams.isEmpty)
              val uninitCd = tc.uninitClasses.init2cd(clsId).cd
              val selIx = origCd.fields.indexWhere(_.id == selector)
              val fieldInfo = tc.classesConsInfo(clsId).fields(selector)
              val newSel = uninitCd.fields(selIx)
              (newSel.id, CtxKind.ConstructionOrBinding(fieldInfo.fullyInit, fieldInfo.nullable, newSel.tpe))
            }
          }
          val valueRec = transform(value, Env(valueCtxKind, env.bdgs))
          FieldAssignment(recvRec, selId, valueRec).copiedFrom(e)
          */

        case IfExpr(cond, thenn, elze) =>
          val condRec = transform(cond, env.withPureCtx)
          val thennRec = transform(thenn, env)
          val elzeRec = transform(elze, env)
          IfExpr(condRec, thennRec, elzeRec).copiedFrom(e)

        case Block(exprs, last) =>
          val exprsRec = exprs.map(transform(_, env.withPureCtx))
          val lastRec = transform(last, env)
          Block(exprsRec, lastRec).copiedFrom(e)

        case MatchExpr(scrutinee, cases) =>
          val scrutRec = transform(scrutinee, env.withPureCtx)
          val casesRec = cases.map { cse =>
            val guardRec = cse.optGuard.map(transform(_, env.withPureCtx))
            val rhsRec = transform(cse.rhs, env)
            MatchCase(cse.pattern, guardRec, rhsRec).copiedFrom(cse)
          }
          MatchExpr(scrutRec, casesRec).copiedFrom(e)

        case LetRec(fds, body) =>
          val fdsRec = fds.map(fd => fd.copy(fullBody = transform(fd.fullBody, env.withPureCtx)))
          val bodyRec = transform(body, env)
          LetRec(fdsRec, bodyRec).copiedFrom(e)

        case Assert(pred, err, body) =>
          val predRec = transform(pred, env.withPureCtx)
          val bodyRec = transform(body, env)
          Assert(predRec, err, bodyRec).copiedFrom(e)

        case Assume(pred, body) =>
          val predRec = transform(pred, env.withPureCtx)
          val bodyRec = transform(body, env)
          Assume(predRec, bodyRec).copiedFrom(e)

        case Require(pred, body) =>
          val predRec = transform(pred, env.withPureCtx)
          val bodyRec = transform(body, env)
          Require(predRec, bodyRec).copiedFrom(e)

        case Decreases(pred, body) =>
          val predRec = transform(pred, env.withPureCtx)
          val bodyRec = transform(body, env)
          Decreases(predRec, bodyRec).copiedFrom(e)

        case Ensuring(body, pred) =>
          val bodyRec = transform(body, env)
          val predRec = transform(pred, env.withPureCtx)
          Ensuring(bodyRec, predRec.asInstanceOf[Lambda]).copiedFrom(e)

        case Operator(es, recons) =>
          ???
          /*
          val eTpe = e.getType(using tc.symbols)
          val esRec = es.map(transform(_, env.withPureCtx))
          val e2 = recons(esRec).copiedFrom(e)
          // TODO: Use adaptExpression?
          val (resFullyInit, resNullable) = env.ctxKind.fullyInitAndNullable
          val (e3, e3Tpe) = {
            if (resFullyInit) (e2, eTpe)
            else {
              val ClassType(clsId, clsTps) = getAsClassType(eTpe) // TODO: Nope
              assert(clsTps.isEmpty)
              val uninitCd = tc.uninitClasses.init2cd(clsId)
              // TODO: May need cast (non-sealed)
              (FunctionInvocation(uninitCd.fromInitId, clsTps, Seq(e2)).copiedFrom(e), ClassType(uninitCd.cd.id, clsTps))
            }
          }
          if (resNullable) some(e3, e3Tpe) else e3
          */
      }
    }

    def none(tpe: Type): Expr = ClassConstructor(ClassType(tc.optionMutDefs.none.id, Seq(tpe)), Seq.empty)
    def some(e: Expr, tpe: Type): Expr = ClassConstructor(ClassType(tc.optionMutDefs.some.id, Seq(tpe)), Seq(e))
    def get(e: Expr): Expr = MethodInvocation(e, tc.optionMutDefs.get.id, Seq.empty, Seq.empty)

    def adaptVariableType(vtpe: Type, fullyInit: Boolean, nullable: Boolean): Type = {
      val tpe2 = {
        if (fullyInit) vtpe
        else vtpe match {
          case ClassType(clsId, clsTps) =>
            assert(clsTps.isEmpty)
            ClassType(tc.uninitClasses.init2cd(clsId).cd.id, clsTps)
          // TODO: What about array of array of uninit???
          case ArrayType(ClassType(clsId, clsTps)) =>
            assert(clsTps.isEmpty)
            ArrayType(ClassType(tc.uninitClasses.init2cd(clsId).cd.id, clsTps))
        }
      }
      if (!nullable) tpe2
      else ClassType(tc.optionMutDefs.option.id, Seq(tpe2))
    }

    def letCase(vd: ValDef, e: Expr, body: Expr, env: Env)(mkLet: (ValDef, Expr, Expr) => Expr): Expr = {
      val eInfo = exprInfoOf(e, env.bdgs.view.mapValues(_.info).toMap)
      val newVdTpe = adaptVariableType(vd.tpe, eInfo.fullyInit, eInfo.nullable)
      val eRec = transform(e, Env(CtxKind.ConstructionOrBinding(eInfo.fullyInit, eInfo.nullable, newVdTpe), env.bdgs))
      val bodyRec = transform(body, Env(env.ctxKind, env.bdgs + (vd.toVariable -> BdgInfo(eInfo, newVdTpe))))
      mkLet(vd.copy(tpe = newVdTpe), eRec, bodyRec).copiedFrom(e)
    }
  }

  case class UninitClassDefs(init2cd: Map[Identifier, UninitClassDef],
                             uninit2init: Map[Identifier, Identifier]) {
    def allNewClasses: Seq[ClassDef] = init2cd.values.map(_.cd).toSeq
    def allNewFunctions: Seq[FunDef] = init2cd.values.flatMap {
      case p: UninitClassDef.Parent => Seq(p.isInit, p.toInitFd, p.fromInitFd, p.isInitArr, p.toInitArrFd, p.fromInitArrFd)
      case _: UninitClassDef.LeafOrIntermediate => Seq.empty
    }.toSeq
  }
  enum UninitClassDef {
    case Parent(cd_ : ClassDef, isInit: FunDef, toInitFd: FunDef, fromInitFd: FunDef, isInitArr: FunDef, toInitArrFd: FunDef, fromInitArrFd: FunDef, hasDescendants: Boolean)
    case LeafOrIntermediate(cd_ : ClassDef, isInitId_ : Identifier, toInitId_ : Identifier, fromInitId_ : Identifier, isInitArrId_ : Identifier, toInitArrId_ : Identifier, fromInitArrId_ : Identifier)

    def cd: ClassDef = this match {
      case p: Parent => p.cd_
      case li: LeafOrIntermediate => li.cd_
    }
    def isInitId: Identifier = this match {
      case p: Parent => p.isInit.id
      case li: LeafOrIntermediate => li.isInitId_
    }
    def toInitId: Identifier = this match {
      case p: Parent => p.toInitFd.id
      case li: LeafOrIntermediate => li.toInitId_
    }
    def fromInitId: Identifier = this match {
      case p: Parent => p.fromInitFd.id
      case li: LeafOrIntermediate => li.fromInitId_
    }
    def isInitArrId: Identifier = this match {
      case p: Parent => p.isInitArr.id
      case li: LeafOrIntermediate => li.isInitArrId_
    }
    def fromInitArrId: Identifier = this match {
      case p: Parent => p.fromInitArrFd.id
      case li: LeafOrIntermediate => li.fromInitArrId_
    }
    def toInitArrId: Identifier = this match {
      case p: Parent => p.toInitArrFd.id
      case li: LeafOrIntermediate => li.toInitArrId_
    }
  }

  private def createUninitClasses(symbols: Symbols,
                                  optionMutDefs: OptionMutDefs,
                                  classesConsInfo: Map[Identifier, ClassConsInfo]): UninitClassDefs = {
    import scala.collection.mutable
    import symbols._
    import exprOps._
    given Symbols = symbols

    def topParentOf(cls: Identifier): Identifier = {
      val parents = symbols.classes(cls).parents
      // Though a ClassDef supports for multiple parents, Stainless only supports for single inheritance
      // (see FragmentChecker)
      assert(parents.size <= 1)
      if (parents.isEmpty) cls
      else topParentOf(parents.head.id)
    }
    def descendants(cls: Identifier): Set[Identifier] = {
      val children = symbols.classes(cls).children
      if (children.isEmpty) Set(cls)
      else Set(cls) ++ children.flatMap(c => descendants(c.id) + c.id).toSet
    }

    // TODO: issealed: we must require all known hierarchy

    val initNeedUninit = classesConsInfo.filter(_._2.needsUninit).keySet
    val needUninit = mutable.HashSet.empty[Identifier]
    val topParentOfMap = mutable.Map.empty[Identifier, Identifier]
    val descendantsMap = mutable.Map.empty[Identifier, Set[Identifier]]
    for (cls <- initNeedUninit) {
      val p = topParentOf(cls)
      if (!needUninit(p)) {
        val desc = descendants(p)
        assert(desc(cls))
        assert(desc(p))
        needUninit ++= desc
        desc.foreach(topParentOfMap += _ -> p)
        descendantsMap(p) = desc
      }
      // otherwise: we've already processed this hierarchy
    }
    for (cls <- needUninit; if !descendantsMap.contains(cls)) {
      val desc = descendants(cls)
      assert(desc(cls))
      descendantsMap(cls) = desc
    }

    def isAbstract(cls: Identifier): Boolean = {
      val res = descendantsMap(cls).size > 1
      // Sanity check
      assert(symbols.classes(cls).isAbstract == res)
      res
    }
    def isLeaf(cls: Identifier): Boolean = {
      val res = descendantsMap(cls).size == 1
      // Sanity check
      assert(!symbols.classes(cls).isAbstract == res)
      res
    }
    def isTopParent(cls: Identifier): Boolean = topParentOfMap(cls) == cls

    topParentOfMap.values.find(p => !symbols.classes(p).isSealed && !isLeaf(p)) match {
      case Some(p) => throw MalformedStainlessCode(symbols.classes(p), "Cannot use uninitialized fields on non-sealed hierarchies")
      case None => ()
    }

    //////////////////////////////////////////
    def generateFnIdentifier(nme: String): Map[Identifier, Identifier] = {
      // 1 fn per hierarchy
      val fnIds = topParentOfMap.values.toSet.map(_ -> (ast.SymbolIdentifier(nme) : Identifier)).toMap
      // All the classes of the same hierarchy get that fn name
      needUninit.map(cls => cls -> fnIds(topParentOfMap(cls))).toMap
    }

    val init2uninit = needUninit.map(id => id -> (ast.SymbolIdentifier(s"${id.name}Uninit"): Identifier)).toMap
    val uninit2init = init2uninit.map { case (init, uninit) => (uninit, init) }

    def createNewFields(cls: Identifier): Seq[ValDef] = {
      val origCD = symbols.getClass(cls)
      if (isLeaf(cls)) {
        val info = classesConsInfo(cls)
        origCD.fields.map { origVd =>
          val fldInfo = info.fields(origVd.id)

          if (!fldInfo.nullable && fldInfo.fullyInit) {
            ValDef(origVd.id.freshen, origVd.tpe, origVd.flags)
          } else {
            val tpe2 = {
              if (!fldInfo.fullyInit) {
                val ClassType(fldCtId, fldTps) = getAsClassType(origVd.tpe) // TODO: Non, array
                assert(init2uninit.contains(fldCtId))
                ClassType(init2uninit(fldCtId), fldTps)
              } else origVd.tpe
            }
            val tpe3 = {
              if (fldInfo.nullable) {
                ClassType(optionMutDefs.option.id, Seq(tpe2))
              } else {
                tpe2
              }
            }

            ValDef(origVd.id.freshen, tpe3, origVd.flags)
          }
        }
      } else {
        // Abstract classes do not have fields
        assert(origCD.fields.isEmpty)
        Seq.empty
      }
    }
    val isInitIds = generateFnIdentifier("isInit")
    val toInitIds = generateFnIdentifier("toInit")
    val fromInitIds = generateFnIdentifier("fromInit")
    val isInitArrIds = generateFnIdentifier("isInitArr")
    val toInitArrIds = generateFnIdentifier("toInitArr")
    val fromInitArrIds = generateFnIdentifier("fromInitArr")
    val newFieldsMap: Map[Identifier, Seq[ValDef]] = needUninit.map(cls => cls -> createNewFields(cls)).toMap

    def createUninitClass(cls: Identifier): UninitClassDef = {
      val parent = topParentOfMap(cls)
      val info = classesConsInfo(cls)
      val origCD = symbols.getClass(cls)
      assert(origCD.typeArgs.isEmpty)

      val newFields = newFieldsMap(cls)
      val newParents = origCD.parents.map(ct => ClassType(init2uninit(ct.id), Seq.empty))
      val newCd = new ClassDef(
        init2uninit(cls),
        Seq.empty,
        newParents,
        newFields,
        (origCD.flags :+ IsMutable).distinct
      )
      if (isTopParent(cls)) {
        val isInitFd = mkIsInitFd(cls)
        val toInitFd = mkToInitFd(cls)
        val fromInitFd = mkFromInitFd(cls)
        val isInitArrFd = mkIsInitArrFd(cls)
        val toInitArrFd = mkToInitArrFd(cls)
        val fromInitArrFd = mkFromInitArrFd(cls)
        UninitClassDef.Parent(newCd,
          isInit = isInitFd, toInitFd = toInitFd, fromInitFd = fromInitFd,
          isInitArr = isInitArrFd, toInitArrFd = toInitArrFd, fromInitArrFd = fromInitArrFd,
          hasDescendants = !isLeaf(cls))
      } else {
        UninitClassDef.LeafOrIntermediate(newCd,
          isInitId_ = isInitIds(cls), toInitId_ = toInitIds(cls), fromInitId_ = fromInitIds(cls),
          isInitArrId_ = isInitArrIds(cls), toInitArrId_ = toInitArrIds(cls), fromInitArrId_ = fromInitArrIds(cls))
      }
    }

    def getUnderlyingUninitIdOf(info: FieldInfo, newFld: ValDef): Identifier = {
      val ClassType(fldClsId, tps) = getAsClassType(newFld.tpe) // TODO: Non, array
      if (info.nullable) {
        assert(fldClsId == optionMutDefs.option.id && tps.size == 1)
        val ClassType(fldClsId2, tps2) = getAsClassType(tps.head) // TODO: Non, array
        assert(tps2.isEmpty)
        fldClsId2
      } else {
        assert(tps.isEmpty)
        fldClsId
      }
    }

    def mkMatchExpr(scrut: Expr, origCls: Identifier)
                   (ctOfLeafCls: Identifier => ClassType)
                   (bodyBuilder: (Variable, Identifier) => Expr): MatchExpr = {
      val allLeafs = descendantsMap(origCls).filter(isLeaf)
      val cases = allLeafs.toSeq.map { leafCls =>
        val ct = ctOfLeafCls(leafCls)
        val binder = ValDef(FreshIdentifier(leafCls.name.take(1).toLowerCase), ct)
        val nbFields = symbols.classes(leafCls).fields.size
        val pat = ClassPattern(Some(binder), ct, Seq.fill(nbFields)(WildcardPattern(None)))
        val rhs = bodyBuilder(binder.toVariable, leafCls)
        MatchCase(pat, None, rhs)
      }
      MatchExpr(scrut, cases)
    }

    def mkIsInitFd(origCls: Identifier): FunDef = {
      val uninitCls = init2uninit(origCls)

      def bodyBuilder(recv: Expr, origCls: Identifier): Expr = {
        val info = classesConsInfo(origCls)
        val origField = classes(origCls).fields
        val uninitCls = init2uninit(origCls)

        val conjs = info.fields
          .filter { case (_, info) => info.nullable || !info.fullyInit }
          .flatMap { case (origFld, info) =>
            val fldIx = origField.indexWhere(_.id == origFld)
            val newFld = newFieldsMap(origCls)(fldIx)
            val sel = ClassSelector(recv, newFld.id)
            val isDefined = {
              if (info.nullable) Seq(MethodInvocation(sel, optionMutDefs.isDefined.id, Seq.empty, Seq.empty))
              else Seq.empty[Expr]
            }
            val fldGet = {
              if (info.nullable) MethodInvocation(sel, optionMutDefs.get.id, Seq.empty, Seq.empty)
              else sel
            }
            val isInit = {
              if (!info.fullyInit) {
                val fldClsUninit = getUnderlyingUninitIdOf(info, newFld)
                val fldClsInit = uninit2init(fldClsUninit)
                Seq(MethodInvocation(fldGet, isInitIds(fldClsInit), Seq.empty, Seq.empty))
              } else Seq.empty[Expr]
            }
            isDefined ++ isInit
          }.toSeq
        andJoin(conjs)
      }

      val body = {
        val thiss = This(ClassType(uninitCls, Seq.empty))
        if (isLeaf(origCls)) bodyBuilder(thiss, origCls)
        else mkMatchExpr(thiss, origCls)(leafCls => ClassType(init2uninit(leafCls), Seq.empty))(bodyBuilder)
      }
      new FunDef(
        isInitIds(origCls),
        Seq.empty,
        Seq.empty,
        BooleanType(),
        body,
        Seq(IsMethodOf(uninitCls), Final, Derived(None), IsPure)
      )
    }

    def mkToInitFd(origCls: Identifier): FunDef = {
      val uninitCls = init2uninit(origCls)

      def bodyBuilder(recv: Expr, origCls: Identifier): Expr = {
        val infos = classesConsInfo(origCls)
        val origFields = classes(origCls).fields
        val uninitCls = init2uninit(origCls)
        val args = origFields.zipWithIndex.map { case (origField, fldIx) =>
          val newFld = newFieldsMap(origCls)(fldIx)
          val sel = FreshCopy(ClassSelector(recv, newFld.id)) // TODO: !!!! NEED CHECKS TO ENSURE NO MUTATION
          val info = infos.fields(origField.id)
          val get = {
            if (info.nullable) MethodInvocation(sel, optionMutDefs.get.id, Seq.empty, Seq.empty)
            else sel
          }
          if (!info.fullyInit) {
            val fldClsUninit = getUnderlyingUninitIdOf(info, newFld)
            val fldClsInit = uninit2init(fldClsUninit)
            MethodInvocation(get, toInitIds(fldClsInit), Seq.empty, Seq.empty)
          } else get
        }
        ClassConstructor(ClassType(origCls, Seq.empty), args)
      }

      val thiss = This(ClassType(uninitCls, Seq.empty))
      val bodyNoReq = {
        if (isLeaf(origCls)) bodyBuilder(thiss, origCls)
        else mkMatchExpr(thiss, origCls)(leafCls => ClassType(init2uninit(leafCls), Seq.empty))(bodyBuilder)
      }
      val bodyWithReq = Require(MethodInvocation(thiss, isInitIds(origCls), Seq.empty, Seq.empty), bodyNoReq)
      new FunDef(
        toInitIds(origCls),
        Seq.empty,
        Seq.empty,
        ClassType(origCls, Seq.empty),
        bodyWithReq,
        Seq(IsMethodOf(uninitCls), Final, Derived(None), IsPure)
      )
    }

    def mkFromInitFd(origCls: Identifier): FunDef = {
      val uninitCls = init2uninit(origCls)
      val fromInitVd = ValDef(FreshIdentifier("init"), ClassType(origCls, Seq.empty))

      def bodyBuilder(recv: Expr, origCls: Identifier): Expr = {
        val infos = classesConsInfo(origCls)
        val origFields = classes(origCls).fields
        val uninitCls = init2uninit(origCls)
        val args = origFields.zipWithIndex.map { case (origField, fldIx) =>
          val newFld = newFieldsMap(origCls)(fldIx)
          val sel = FreshCopy(ClassSelector(recv, origField.id)) // TODO: !!!! NEED CHECKS TO ENSURE NO MUTATION
          val info = infos.fields(origField.id)
          val fromInit = {
            if (!info.fullyInit) {
              val fldClsUninit = getUnderlyingUninitIdOf(info, newFld)
              val fldClsInit = uninit2init(fldClsUninit)
              FunctionInvocation(fromInitIds(fldClsInit), Seq.empty, Seq(sel))
            }
            else sel
          }
          if (info.nullable) {
            val ClassType(optId, tps) = getAsClassType(newFld.tpe) // TODO: Non, array
            assert(optId == optionMutDefs.option.id && tps.size == 1)
            ClassConstructor(ClassType(optionMutDefs.some.id, tps), Seq(fromInit))
          }
          else fromInit
        }
        ClassConstructor(ClassType(uninitCls, Seq.empty), args)
      }
      val body = {
        if (isLeaf(origCls)) bodyBuilder(fromInitVd.toVariable, origCls)
        else mkMatchExpr(fromInitVd.toVariable, origCls)(ClassType(_, Seq.empty))(bodyBuilder)
      }
      new FunDef(
        fromInitIds(origCls),
        Seq.empty,
        Seq(fromInitVd),
        ClassType(uninitCls, Seq.empty),
        body,
        Seq(Derived(None), IsPure)
      )
    }

    def mkIsInitArrFd(origCls: Identifier): FunDef = {
      import t.dsl._
      val fnId = isInitArrIds(origCls)
      val uninitCls = init2uninit(origCls)
      val arrVd = ValDef(FreshIdentifier("arr"), ArrayType(ClassType(uninitCls, Seq.empty)))
      val fromVd = ValDef(FreshIdentifier("from"), Int32Type())
      val untilVd = ValDef(FreshIdentifier("until"), Int32Type())
      val arr = arrVd.toVariable
      val from = fromVd.toVariable
      val until = untilVd.toVariable
      val body = {
        Require(Int32Literal(0) <= from && from <= until && until <= ArrayLength(arr),
          Decreases(from - until,
            from === until || (MethodInvocation(ArraySelect(arr, from), isInitIds(origCls), Seq.empty, Seq.empty) &&
              FunctionInvocation(fnId, Seq.empty, Seq(arr, from + Int32Literal(1), until)))
          )
        )
      }
      new FunDef(
        fnId,
        Seq.empty,
        Seq(arrVd, fromVd, untilVd),
        BooleanType(),
        NoTree(BooleanType()), // TODO,
        Seq(Derived(None), IsPure)
      )
    }

    def mkToInitArrFd(origCls: Identifier): FunDef = {
      import t.dsl._

      val fnId = toInitArrIds(origCls)
      val uninitCls = init2uninit(origCls)
      val arrVd = ValDef(FreshIdentifier("arr"), ArrayType(ClassType(uninitCls, Seq.empty)))
      val arr = arrVd.toVariable

      val resArrVd = ValDef(FreshIdentifier("resArr"), ArrayType(ClassType(origCls, Seq.empty)))
      val iVd = ValDef(FreshIdentifier("i"), Int32Type())
      val resArr = resArrVd.toVariable
      val i = iVd.toVariable

      val recId = FreshIdentifier("rec")
      val recTpe = FunctionType(Seq(resArr.tpe, i.tpe), resArr.tpe)
      val recBody = {
        // TODO: Require isInit, unfolded
        Require(Int32Literal(0) <= i && i <= ArrayLength(arr) && ArrayLength(arr) === ArrayLength(resArr),
          Decreases(ArrayLength(arr) - i,
            if_(i < ArrayLength(arr)) {
              Block(Seq(
                ArrayUpdate(resArr, i, MethodInvocation(ArraySelect(arr, i), toInitIds(origCls), Seq.empty, Seq.empty))),
                ApplyLetRec(recId, Seq.empty, recTpe, Seq.empty, Seq(resArr, i + Int32Literal(1)))
              )
            } else_ resArr
          )
        )
      }
      val body = {
        val initArrayVd = ValDef(FreshIdentifier("initArray"), resArr.tpe)
        val initArray = Choose(initArrayVd, ArrayLength(initArrayVd.toVariable) === ArrayLength(arr))
        Require(FunctionInvocation(isInitArrIds(origCls), Seq.empty, Seq(arr, Int32Literal(0), ArrayLength(arr))),
          LetRec(
            Seq(LocalFunDef(recId, Seq.empty, Seq(resArrVd, iVd), resArr.tpe, recBody, Seq.empty)),
            ApplyLetRec(recId, Seq.empty, recTpe, Seq.empty, Seq(Int32Literal(0), initArray))
          )
        )
      }
      new FunDef(
        fnId,
        Seq.empty,
        Seq(arrVd),
        resArr.tpe,
        NoTree(resArr.tpe), // TODO
        Seq(Derived(None), IsPure)
      )
    }

    def mkFromInitArrFd(origCls: Identifier): FunDef = {
      import t.dsl._
      val fnId = fromInitArrIds(origCls)
      val arrVd = ValDef(FreshIdentifier("arr"), ArrayType(ClassType(origCls, Seq.empty)))
      val arr = arrVd.toVariable

      val uninitCls = init2uninit(origCls)
      val resArrVd = ValDef(FreshIdentifier("resArr"), ArrayType(ClassType(uninitCls, Seq.empty)))
      val iVd = ValDef(FreshIdentifier("i"), Int32Type())
      val resArr = resArrVd.toVariable
      val i = iVd.toVariable

      new FunDef(
        fnId,
        Seq.empty,
        Seq(arrVd),
        resArr.tpe,
        NoTree(resArr.tpe), // TODO
        Seq(Derived(None), IsPure)
      )
    }

    val init2cd = init2uninit.keySet.map(id => id -> createUninitClass(id)).toMap
    UninitClassDefs(init2cd, uninit2init)
  }

  case class ClassConsInfo(fields: Map[Identifier, FieldInfo]) {
    def setNullable(fld: Identifier): ClassConsInfo = {
      assert(fields.contains(fld))
      ClassConsInfo(fields.updatedWith(fld)(_.map(_.copy(nullable = true))))
    }
    def setUninit(fld: Identifier): ClassConsInfo = {
      assert(fields.contains(fld))
      ClassConsInfo(fields.updatedWith(fld)(_.map(_.copy(fullyInit = false))))
    }
    def needsUninit: Boolean = fields.values.exists(fi => !fi.fullyInit || fi.nullable)
  }

  case class FieldInfo(nullable: Boolean, fullyInit: Boolean)

  private class UninitClassesCollector(using symbols: Symbols) extends inox.transformers.Traverser {
    override val trees: s.type = s
    case class Env(bSel: BranchingSelections,
                   bdgsSels: Map[Variable, BranchingSelections],
                   bdgsNullable: Map[Variable, NullableSelections]) {
      def resetSelectionCtx: Env = copy(bSel = BranchingSelections.Leaf)
      def ::(fld: Identifier): Env = copy(bSel = fld :: bSel)
      def +(kv: (Variable, (BranchingSelections, NullableSelections))): Env =
        Env(bSel, bdgsSels + (kv._1 -> kv._2._1), bdgsNullable + (kv._1 -> kv._2._2))
    }
    object Env {
      def init: Env = Env(BranchingSelections.Leaf, Map.empty, Map.empty)
    }

    var classesNullableSelections: Map[Identifier, NullableSelections] =
      symbols.classes.keySet.map(_ -> NullableSelections.empty).toMap

    val fieldsOfClass: Map[Identifier, Identifier] = {
      symbols.classes.flatMap { case (clsId, cd) =>
        cd.fields.map(_.id -> clsId).toMap
      }
    }

    override def traverse(e: Expr, ctx: Env): Unit = {
//      println(s"$e -> $ctx")
      e match {
        case NullLit() =>
          /*
          val last = ctx.fieldsSel.lastFields
          for (fld <- last) {
            val cls = fieldsOfClass(fld)
            classesConsInfo = classesConsInfo.updated(cls, classesConsInfo(cls).setNullable(fld))
          }
          val woLast = ctx.fieldsSel.withoutLastFields.allFields
          for (fld <- woLast) {
            val cls = fieldsOfClass(fld)
            classesConsInfo = classesConsInfo.updated(cls, classesConsInfo(cls).setUninit(fld))
          }
          */
        case v: Variable =>
          /*
          ctx.bdgs.get(v) match {
            case Some(ExprInfo(_, fullyInit, nullable)) =>
              if (!fullyInit || nullable) {
                val last = ctx.fieldsSel.lastFields
                for (fld <- last) {
                  val cls = fieldsOfClass(fld)
                  if (!fullyInit) {
                    classesConsInfo = classesConsInfo.updated(cls, classesConsInfo(cls).setUninit(fld))
                  }
                  if (nullable) {
                    classesConsInfo = classesConsInfo.updated(cls, classesConsInfo(cls).setNullable(fld))
                  }
                }
                val woLast = ctx.fieldsSel.withoutLastFields.allFields
                for (fld <- woLast) {
                  val cls = fieldsOfClass(fld)
                  classesConsInfo = classesConsInfo.updated(cls, classesConsInfo(cls).setUninit(fld))
                }
              }
            case None => ()
          }
          */

        case ClassConstructor(ct, args) =>
          if (ct.tps.nonEmpty) {
            val argsNullable = args.foldLeft(NullableSelections.empty)(_ ++ nullableSelections(_, ctx.bdgsNullable))
            if (argsNullable.isNullable || argsNullable.isUninit) {
              throw MalformedStainlessCode(e, "Cannot have uninitialized or nullable fields for parametric classes")
            }
          }
          val cd = symbols.getClass(ct.id)
          assert(cd.fields.size == args.size)
          for ((fld, arg) <- cd.fields zip args) {
            traverse(arg, fld.id :: ctx)
          }

        case FieldAssignment(recv, selector, value) =>
          traverse(recv, ctx.resetSelectionCtx)
          val recvSels = activeSelections(recv, ctx.bdgsSels)
          traverse(value, selector :: ctx)

        case ClassSelector(recv, selector) =>
          traverse(recv, ctx.resetSelectionCtx)

        // TODO: ArrayUpdateD ?
        case FiniteArray(elems, _) =>
          for (elem <- elems) {
            traverse(elem, ctx.copy(bSel = Selection.Array :: ctx.bSel))
          }

        case LargeArray(elems, default, sze, _) =>
          assert(elems.isEmpty, "What, this elems is actually populated with something???")
          traverse(sze, ctx.resetSelectionCtx)
          traverse(default, ctx.copy(bSel = Selection.Array :: ctx.bSel))

        case ArraySelect(arr, ix) =>
          traverse(arr, ctx.resetSelectionCtx)
          traverse(ix, ctx.resetSelectionCtx)

        case ArrayUpdate(arr, ix, value) =>
          traverse(arr, ctx.resetSelectionCtx)
          traverse(ix, ctx.resetSelectionCtx)
          val arrSels = activeSelections(arr, ctx.bdgsSels)
          traverse(value, ctx.copy(bSel = Selection.Array :: arrSels))

        case Let(vd, e, body) =>
          val eSels = activeSelections(e, ctx.bdgsSels)
          val eNullable = nullableSelections(e, ctx.bdgsNullable)
          traverse(e, ctx.resetSelectionCtx)
          traverse(body, ctx + (vd.toVariable -> (eSels, eNullable)))

        case LetVar(vd, e, body) =>
          val eSels = activeSelections(e, ctx.bdgsSels)
          val eNullable = nullableSelections(e, ctx.bdgsNullable)
          traverse(e, ctx.resetSelectionCtx)
          traverse(body, ctx + (vd.toVariable -> (eSels, eNullable)))

        case IfExpr(cond, thenn, elze) =>
          traverse(cond, ctx.resetSelectionCtx)
          traverse(thenn, ctx)
          traverse(elze, ctx)

        case MatchExpr(scrutinee, cases) =>
          traverse(scrutinee, ctx.resetSelectionCtx)
          for (c <- cases) {
            c.optGuard.foreach(traverse(_, ctx.resetSelectionCtx))
            traverse(c.rhs, ctx)
          }

        case Block(exprs, last) =>
          exprs.foreach(traverse(_, ctx.resetSelectionCtx))
          traverse(last, ctx)

        case LetRec(fds, body) =>
          fds.foreach(fd => traverse(fd.fullBody, ctx.resetSelectionCtx))
          traverse(body, ctx)

        case Assert(pred, _, body) =>
          traverse(pred, ctx.resetSelectionCtx)
          traverse(body, ctx)

        case Assume(pred, body) =>
          traverse(pred, ctx.resetSelectionCtx)
          traverse(body, ctx)

        case Decreases(pred, body) =>
          traverse(pred, ctx.resetSelectionCtx)
          traverse(body, ctx)

        case Require(pred, body) =>
          traverse(pred, ctx.resetSelectionCtx)
          traverse(body, ctx)

        case Ensuring(body, pred) =>
          traverse(body, ctx)
          traverse(pred, ctx.resetSelectionCtx)

        case Operator((es, _)) =>
          es.foreach(traverse(_, ctx.resetSelectionCtx))
      }
    }
  }

  // TODO: Also for array
  // Note: this goes from "bottom" to "top"
  private enum FieldsSel {
    case Field(fld: Identifier, tail: FieldsSel)
    case Branch(branches: Seq[FieldsSel])
    case Leaf()

    def ::(fld: Identifier): FieldsSel = this match {
      case Field(fld2, tail) => Field(fld, Field(fld2, tail))
      case Branch(branches) => Branch(branches.map(fld :: _))
      case Leaf() => Field(fld, Leaf())
    }

    def allFields: Seq[Identifier] = this match {
      case Field(fld, tail) => fld +: tail.allFields
      case Branch(branches) => branches.flatMap(_.allFields)
      case Leaf() => Seq.empty
    }

    def lastFields: Seq[Identifier] = this match {
      case Field(fld, _) => Seq(fld)
      case Branch(branches) => branches.flatMap(_.lastFields)
      case Leaf() => Seq.empty
    }

    def withoutLastFields: FieldsSel = this match {
      case Field(_, tail) => tail
      case Branch(branches) => Branch(branches.map(_.withoutLastFields))
      case Leaf() => Leaf()
    }
  }

  private object FieldsSel {
    def fromSeq(flds: Seq[Identifier]): FieldsSel = {
      if (flds.isEmpty) Leaf()
      else FieldsSel.Field(flds.head, fromSeq(flds.tail))
    }
  }

  private case class ExprInfo(fieldsSel: FieldsSel, fullyInit: Boolean, nullable: Boolean)
  private object ExprInfo {
    def empty: ExprInfo = ExprInfo(FieldsSel.Leaf(), fullyInit = true, nullable = false)
  }
  // TODO: curr: FieldsSel?
  private def exprInfoOf(e: Expr, bdgs: Map[Variable, ExprInfo]): ExprInfo = {
    def goBranches(branches: Seq[Expr], bdgs: Map[Variable, ExprInfo]): ExprInfo = {
      val rec = branches.map(go(_, FieldsSel.Leaf(), bdgs))
      val fieldsSel = FieldsSel.Branch(rec.map(_.fieldsSel))
      val fullyInit = rec.forall(_.fullyInit)
      val nullable = rec.exists(_.nullable)
      ExprInfo(fieldsSel, fullyInit, nullable)
    }
    // TODO: Array
    // TODO: ArrayUpdated?
    def go(e: Expr, curr: FieldsSel, bdgs: Map[Variable, ExprInfo]): ExprInfo = e match {
      case NullLit() =>
        assert(curr == FieldsSel.Leaf())
        ExprInfo(FieldsSel.Leaf(), fullyInit = true, nullable = true)
      case v: Variable =>
        assert(curr == FieldsSel.Leaf())
        bdgs.getOrElse(v, ExprInfo.empty)
      case ClassConstructor(_, args) =>
        assert(curr == FieldsSel.Leaf())
        val rec = args.map(go(_, FieldsSel.Leaf(), bdgs))
        val fullyInit = rec.forall(ei => ei.fullyInit && !ei.nullable)
        ExprInfo(FieldsSel.Leaf(), fullyInit, false) // Not nullable since we are constructing a class
      case FiniteArray(elems, _) =>
        val elemsRec = elems.map(go(_, FieldsSel.Leaf(), bdgs))
        val fullyInit = elemsRec.forall(_.fullyInit)
        ExprInfo(FieldsSel.Leaf(), fullyInit, false) // Not nullable because we are constructing an array
      case LargeArray(elems, default, _, _) =>
        assert(elems.isEmpty, "What, this elems is actually populated with something???")
        val defaultRec = go(default, FieldsSel.Leaf(), bdgs)
        ExprInfo(FieldsSel.Leaf(), defaultRec.fullyInit, false) // Not nullable because we are constructing an array

      // TODO: ArraySelect

      case ClassSelector(recv, selector) =>
        val recRecv = exprInfoOf(recv, bdgs)
        val resFieldsSel = selector :: recRecv.fieldsSel
        // TODO: Quid utilisation pour eliminator?
        ExprInfo(selector :: recRecv.fieldsSel, recRecv.fullyInit, recRecv.nullable) // TODO: recRecv nullable dépend aussi du field non???
      case Let(v, e, body) =>
        // TODO: curr?
        val eRec = exprInfoOf(e, bdgs)
        go(body, curr, bdgs + (v.toVariable -> eRec))
      case LetVar(v, e, body) =>
        // TODO: curr?
        val eRec = exprInfoOf(e, bdgs)
        go(body, curr, bdgs + (v.toVariable -> eRec))
      case IfExpr(_, thenn, elze) =>
        assert(curr == FieldsSel.Leaf())
        goBranches(Seq(thenn, elze), bdgs)
      case MatchExpr(_, cases) =>
        assert(curr == FieldsSel.Leaf())
        goBranches(cases.map(_.rhs), bdgs)
      case Block(_, last) => go(last, curr, bdgs)
      case LetRec(_, body) => go(body, curr, bdgs)
      case Assert(_, _, body) => go(body, curr, bdgs)
      case Assume(_, body) => go(body, curr, bdgs)
      case Decreases(_, body) => go(body, curr, bdgs)
      case Require(_, body) => go(body, curr, bdgs)
      case Ensuring(body, _) => go(body, curr, bdgs)
      case _ => ExprInfo.empty
    }
    go(e, FieldsSel.Leaf(), bdgs)
  }

  enum Selection {
    case Field(id: Identifier)
    case Array
  }

  enum BranchingSelections {
    case Single(sel: Selection, tail: BranchingSelections)
    case Branch(branches: Seq[BranchingSelections]) // TODO: Ensures no Leaf in branches
    case Leaf // TODO: !!! Ne pas interpreter necessairement comme "nullable" !!!!

    def ::(fld: Identifier): BranchingSelections = Selection.Field(fld) :: this

    def ::(sel: Selection): BranchingSelections = this match {
      case Single(sel2, tail) => Single(sel, Single(sel2, tail))
      case Branch(branches) => Branch(branches.map(sel :: _))
      case Leaf => Single(sel, Leaf)
    }

    /*
    def allFields: Seq[Identifier] = this match {
      case Field(fld, tail) => fld +: tail.allFields
      case Branch(branches) => branches.flatMap(_.allFields)
      case Leaf => Seq.empty
    }

    def lastFields: Seq[Identifier] = this match {
      case Field(fld, _) => Seq(fld)
      case Branch(branches) => branches.flatMap(_.lastFields)
      case Leaf => Seq.empty
    }
    def withoutLastFields: Selections = this match {
      case Field(_, tail) => tail
      case Branch(branches) => Branch(branches.map(_.withoutLastFields))
      case Leaf => Leaf
    }
    */
  }
  case class Selections(path: Seq[Selection]) {
    def :+(sel: Selection): Selections = Selections(path :+ sel)
    def :+(fld: Identifier): Selections = this :+ Selection.Field(fld)
    def ++(other: Selections): Selections = Selections(path ++ other.path)
    def ::(fld: Identifier): Selections = Selection.Field(fld) :: this
    def ::(sel: Selection): Selections = Selections(sel +: path)
  }
  object Selections {
    def empty: Selections = Selections(Seq.empty)
  }

  case class NullableSelections(sels: Set[Selections]) {
    def isNullable: Boolean = sels(Selections.empty)
    def isUninit: Boolean = sels.exists(_.path.nonEmpty)
    def ++(other: NullableSelections): NullableSelections = NullableSelections(sels ++ other.sels)
    def filter(prefix: Selection): NullableSelections =
      NullableSelections(sels.flatMap { sels =>
        // TODO: What if recv itself is nullable?
        if (sels.path.nonEmpty && sels.path.head == prefix) Some(Selections(sels.path.tail))
        else None
      })
    def :::(prefix: Selections): NullableSelections = NullableSelections(sels.map(prefix ++ _))
    def ::(fld: Identifier): NullableSelections = Selection.Field(fld) :: this
    def ::(sel: Selection): NullableSelections = NullableSelections(sels.map(sel :: _))
  }
  object NullableSelections {
    def empty: NullableSelections = NullableSelections(Set.empty)
  }

  private def nullableSelections(e: Expr, bdgs: Map[Variable, NullableSelections])(using symbols: Symbols): NullableSelections = {
    def go(e: Expr, bdgs: Map[Variable, NullableSelections]): NullableSelections = e match {
      case NullLit() =>
        NullableSelections(Set(Selections.empty))
      case v: Variable =>
        bdgs.getOrElse(v, NullableSelections.empty)
      case ClassConstructor(ct, args) =>
        val fields = symbols.getClass(ct.id).fields
        assert(args.size == fields.size)
        val rec = fields.zip(args).flatMap { case (field, arg) => (field.id :: go(arg, bdgs)).sels }.toSet
        NullableSelections(rec)
      // TODO: ArrayUpdateD ?
      case FiniteArray(elems, _) =>
        val rec = elems.flatMap(e => (Selection.Array :: go(e, bdgs)).sels).toSet
        NullableSelections(rec)
      case LargeArray(elems, default, _, _) =>
        assert(elems.isEmpty, "What, this elems is actually populated with something???")
        Selection.Array :: go(default, bdgs)
      case ClassSelector(recv, sel) =>
        // TODO: What if recv itself is nullable?
        go(recv, bdgs).filter(Selection.Field(sel))
      case ArraySelect(arr, _) =>
        // TODO: What if arr itself is nullable?
        go(arr, bdgs).filter(Selection.Array)
      case Let(v, e, body) =>
        val eRec = go(e, bdgs)
        go(body, bdgs + (v.toVariable -> eRec))
      case LetVar(v, e, body) =>
        val eRec = go(e, bdgs)
        go(body, bdgs + (v.toVariable -> eRec))
      case IfExpr(_, thenn, elze) =>
        val rec = Seq(thenn, elze).flatMap(go(_, bdgs).sels).toSet
        NullableSelections(rec)
      case MatchExpr(_, cases) =>
        val rec = cases.map(_.rhs).flatMap(go(_, bdgs).sels).toSet
        NullableSelections(rec)
      case Block(_, last) => go(last, bdgs)
      case LetRec(_, body) => go(body, bdgs)
      case Assert(_, _, body) => go(body, bdgs)
      case Assume(_, body) => go(body, bdgs)
      case Decreases(_, body) => go(body, bdgs)
      case Require(_, body) => go(body, bdgs)
      case Ensuring(body, _) => go(body, bdgs)
      case _ => NullableSelections.empty
    }
    go(e, bdgs)
  }

  private def activeSelections(e: Expr, bdgs: Map[Variable, BranchingSelections]): BranchingSelections = {
    def goBranches(branches: Seq[Expr], bdgs: Map[Variable, BranchingSelections]): BranchingSelections = {
      val rec = branches.map(go(_, bdgs))
      BranchingSelections.Branch(rec)
    }
    def go(e: Expr, bdgs: Map[Variable, BranchingSelections]): BranchingSelections = e match {
      case v: Variable =>
        bdgs.getOrElse(v, BranchingSelections.Leaf)
      case ArraySelect(arr, _) =>
        Selection.Array :: go(arr, bdgs)
      case ClassSelector(recv, selector) =>
        selector :: go(recv, bdgs)
      case Let(v, e, body) =>
        val eRec = go(e, bdgs)
        go(body, bdgs + (v.toVariable -> eRec))
      case LetVar(v, e, body) =>
        val eRec = go(e, bdgs)
        go(body, bdgs + (v.toVariable -> eRec))
      case IfExpr(_, thenn, elze) =>
        goBranches(Seq(thenn, elze), bdgs)
      case MatchExpr(_, cases) =>
        goBranches(cases.map(_.rhs), bdgs)
      case Block(_, last) => go(last, bdgs)
      case LetRec(_, body) => go(body, bdgs)
      case Assert(_, _, body) => go(body, bdgs)
      case Assume(_, body) => go(body, bdgs)
      case Decreases(_, body) => go(body, bdgs)
      case Require(_, body) => go(body, bdgs)
      case Ensuring(body, _) => go(body, bdgs)
      case _ => BranchingSelections.Leaf
    }
    go(e, bdgs)
  }

  ///////////////////////////////////////////////////////////////////////////

  private def getAsClassType(tpe: Type): ClassType = tpe match {
    case ct: ClassType => ct
    case other => sys.error(s"Expected to have a class type, but got $other")
  }

  case class OptionMutDefs(option: ClassDef, some: ClassDef, none: ClassDef, isDefined: FunDef, get: FunDef) {
    def allNewClasses: Seq[ClassDef] = Seq(option, some, none)
    def allNewFunctions: Seq[FunDef] = Seq(isDefined, get)
  }

  private def mkOptionMutDefs(): OptionMutDefs = {
    import t.dsl._

    val Seq(option, some, none) =
      Seq("OptionMut", "SomeMut", "NoneMut").map(name => ast.SymbolIdentifier("stainless.internal." + name))
    val value = FreshIdentifier("value")

    val optTp = TypeParameter(FreshIdentifier("A"), Seq(IsMutable))
    val optionCD = new ClassDef(
      option,
      Seq(TypeParameterDef(optTp)),
      Seq.empty,
      Seq.empty,
      Seq(IsAbstract, IsSealed, IsMutable)
    )
    val someTp = TypeParameter(FreshIdentifier("A"), Seq(IsMutable))
    val valueVd = ValDef(value, someTp, Seq(IsVar))
    val someCD = new ClassDef(
      some,
      Seq(TypeParameterDef(someTp)),
      Seq(ClassType(option, Seq(someTp))),
      Seq(valueVd),
      Seq(IsMutable)
    )
    val noneTp = TypeParameter(FreshIdentifier("A"), Seq(IsMutable))
    val noneCD = new ClassDef(
      none,
      Seq(TypeParameterDef(noneTp)),
      Seq(ClassType(option, Seq(noneTp))),
      Seq.empty,
      Seq(IsMutable)
    )

    // TODO: Dire pk optionCD.typeArgs
    val optCT = ClassType(optionCD.id, optionCD.typeArgs)
    val someCT = ClassType(someCD.id, optionCD.typeArgs)
    val noneCT = ClassType(noneCD.id, optionCD.typeArgs)
    val thiss = This(ClassType(optionCD.id, optionCD.typeArgs))
    val isDefinedId = ast.SymbolIdentifier("stainless.internal.OptionMut.isDefined")
    val isDefinedFd = mkFunDef(isDefinedId, IsMethodOf(option), Final, Derived(None))() {
      case Seq() => (Seq.empty, BooleanType(), {
        case Seq() => thiss match_ {
          case_(KP2(someCT)(unused))(_ => BooleanLiteral(true))
          case_(KP2(noneCT)())(_ => BooleanLiteral(false))
        }
      })
    }
    val getId = ast.SymbolIdentifier("stainless.internal.OptionMut.get")
    val getFd = mkFunDef(getId, IsMethodOf(option), Final, Derived(None))() {
      case Seq() => (Seq.empty, optTp, {
        case Seq() =>
          Require(
            MethodInvocation(thiss, isDefinedId, Seq.empty, Seq.empty),
            thiss match_ {
              case_(KP2(someCT)("v" :: optTp)) {
                case Seq(v) => v.toVariable
              }
            }
          )
      })
    }
    OptionMutDefs(optionCD, someCD, noneCD, isDefinedFd, getFd)
  }
}

object LocalNullElimination {
  def apply(trees: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends LocalNullElimination(s)(t)
    new Impl(trees, trees)
  }
}