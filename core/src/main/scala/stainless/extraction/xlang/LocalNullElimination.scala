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
                                classesConsInfo: Map[Identifier, ClassConsInfo],
                                uninitClasses: UninitClassDefs) {
    def allNewClasses: Seq[ClassDef] = optionMutDefs.allNewClasses ++ uninitClasses.allNewClasses
    def allNewFunctions: Seq[FunDef] = optionMutDefs.allNewFunctions ++ uninitClasses.allNewFunctions
  }

  override protected def getContext(symbols: s.Symbols): TransformerContext = {
    given s.Symbols = symbols

    val uninitCC = new UninitClassesCollector
    for ((_, fd) <- symbols.functions) {
//      if (fd.id.name.contains("test")) {
      uninitCC.traverse(fd.fullBody, uninitCC.Env(FieldsSel.Leaf(), Map.empty))
//      }
    }

    println(uninitCC.classesConsInfo)

    val optMutDefs = mkOptionMutDefs()

    println("---------------")

    val uninitClasses = createUninitClasses(symbols, optMutDefs, uninitCC.classesConsInfo)
    println(uninitClasses.init2cd.mkString("\n"))

    println("===========================================")
    println("===========================================")

    TransformerContext(symbols, optMutDefs, uninitCC.classesConsInfo, uninitClasses)
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
        val ClassType(clsId, clsTps) = getAsClassType(eOrigTpe)
        assert(clsTps.isEmpty)
        val uninitCd = tc.uninitClasses.init2cd(clsId)
        val e1 = {
          if (eNullable) get(e).copiedFrom(e)
          else e
        }
        val (e2, tpe2) = {
          // TODO: May need cast (non-sealed)
          if (!resFullyInit) {
            (FunctionInvocation(uninitCd.fromInitId, clsTps, Seq(e1)).copiedFrom(e), ClassType(uninitCd.cd.id, clsTps))
          } else {
            (MethodInvocation(e1, uninitCd.toInitId, Seq.empty, Seq.empty).copiedFrom(e), ClassType(clsId, clsTps))
          }
        }
        if (resNullable) some(e2, tpe2) else e2
      } else {
        if (resNullable == !eNullable) {
          if (!resNullable) get(e).copiedFrom(e)
          else some(e, eNewTpe).copiedFrom(e)
        } else e
      }
    }

    override def transform(e: Expr, env: Env): Expr = {
      e match {
        case NullLit() =>
          env.ctxKind match {
            case CtxKind.ConstructionOrBinding(_, nullable, expectedType) =>
              if (!nullable) throw MalformedStainlessCode(e, "Unsupported usage of `null` (construction or binding)")
              val ClassType(id, tps) = getAsClassType(expectedType)
              assert(id == tc.optionMutDefs.option.id && tps.size == 1)
              none(tps.head).copiedFrom(e)
            case CtxKind.FieldSelection(_) => throw MalformedStainlessCode(e, "Unsupported usage of `null` (field selection)")
            case CtxKind.Pure() => throw MalformedStainlessCode(e, "Unsupported usage of `null` (pure context)")
          }
        case v: Variable =>
          val (resFullyInit, resNullable) = env.ctxKind.fullyInitAndNullable
          env.bdgs.get(v) match {
            case Some(BdgInfo(ExprInfo(_, vFullyInit, vNullable), vNewTpe)) =>
              val v2 = v.copy(tpe = vNewTpe)
              adaptExpression(v2, eOrigTpe = v.tpe, eNewTpe = vNewTpe, vFullyInit, vNullable, resFullyInit, resNullable)
            case None =>
              adaptExpression(v, v.tpe, v.tpe, true, false, resFullyInit, resNullable)
          }

        case Let(vd, e, body) => letCase(vd, e, body, env)(Let.apply)
        case LetVar(vd, e, body) => letCase(vd, e, body, env)(LetVar.apply)

        case ClassConstructor(ct, args) =>
          val fieldsOrig = tc.symbols.getClass(ct.id).fields
          val (argsEnv, mustUseUninit) = tc.uninitClasses.init2cd.get(ct.id) match {
            case Some(uninitCd) =>
              assert(ct.tps.isEmpty)
              val argsInfo = args.map(exprInfoOf(_, env.bdgs.view.mapValues(_.info).toMap))
              val argsFullyInit = argsInfo.forall(_.fullyInit)
              val argsNullable = argsInfo.exists(_.nullable)
              val mustUseUninit = !argsFullyInit || argsNullable
              val fieldsInfo = tc.classesConsInfo(ct.id).fields

              val argsEnv = fieldsOrig.zipWithIndex.map { case (field, fieldIx) =>
                val fieldInfo = fieldsInfo(field.id)
                val ctxKind = CtxKind.ConstructionOrBinding(
                  // TODO: Upd comment
                  // If all argument are fully initialized, then so is this one
                  // However, if there is one uninit argument, this argument is uninit as well if
                  // its corresponding field is uninit, otherwise we proceed to a fully initialized construction
                  !mustUseUninit || fieldInfo.fullyInit,
                  // Ditto for nullable
                  mustUseUninit && fieldInfo.nullable,
                  uninitCd.cd.fields(fieldIx).tpe
                )
                Env(ctxKind, env.bdgs)
              }
              (argsEnv, mustUseUninit)
            case None =>
              val argsEnv = fieldsOrig.map(field => Env(CtxKind.ConstructionOrBinding(fullyInit = true, nullable = false, expectedType = field.tpe), env.bdgs))
              (argsEnv, false)
          }
          val recArgs = args.zip(argsEnv).map(transform(_, _))
          val (e1, tpe1) = {
            if (mustUseUninit) {
              assert(ct.tps.isEmpty)
              val newCt = ClassType(tc.uninitClasses.init2cd(ct.id).cd.id, Seq.empty)
              (ClassConstructor(newCt, recArgs), newCt)
            } else (ClassConstructor(ct, recArgs), ct)
          }
          val (resFullyInit, resNullable) = env.ctxKind.fullyInitAndNullable
          adaptExpression(e1, eOrigTpe = ct, eNewTpe = tpe1, !mustUseUninit, false, resFullyInit, resNullable)

        case ClassSelector(recv, selector) =>
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

        case Assignment(v, value) =>
          assert(env.ctxKind == CtxKind.Pure())
          val (ctxKind, newTpe) = env.bdgs.get(v) match {
            case Some(BdgInfo(ExprInfo(_, fullyInit, nullable), newTpe)) =>
              (CtxKind.ConstructionOrBinding(fullyInit, nullable, v.tpe), newTpe)
            case None => (CtxKind.ConstructionOrBinding(fullyInit = true, nullable = false, v.tpe), v.tpe)
          }
          val valueRec = transform(value, Env(ctxKind, env.bdgs))
          Assignment(v.copy(tpe = newTpe), valueRec).copiedFrom(e)

        case fa @ FieldAssignment(recv, selector, value) =>
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
          val eTpe = e.getType(using tc.symbols)
          val esRec = es.map(transform(_, env.withPureCtx))
          val e2 = recons(esRec).copiedFrom(e)
          val (resFullyInit, resNullable) = env.ctxKind.fullyInitAndNullable
          val (e3, e3Tpe) = {
            if (resFullyInit) (e2, eTpe)
            else {
              val ClassType(clsId, clsTps) = getAsClassType(eTpe)
              assert(clsTps.isEmpty)
              val uninitCd = tc.uninitClasses.init2cd(clsId)
              // TODO: May need cast (non-sealed)
              (FunctionInvocation(uninitCd.fromInitId, clsTps, Seq(e2)).copiedFrom(e), ClassType(uninitCd.cd.id, clsTps))
            }
          }
          if (resNullable) some(e3, e3Tpe) else e3
      }
    }

    def none(tpe: Type): Expr = ClassConstructor(ClassType(tc.optionMutDefs.none.id, Seq(tpe)), Seq.empty)
    def some(e: Expr, tpe: Type): Expr = ClassConstructor(ClassType(tc.optionMutDefs.some.id, Seq(tpe)), Seq(e))
    def get(e: Expr): Expr = MethodInvocation(e, tc.optionMutDefs.get.id, Seq.empty, Seq.empty)

    def adaptVariableType(vtpe: Type, fullyInit: Boolean, nullable: Boolean): Type = {
      val tpe2 = {
        if (fullyInit) vtpe
        else {
          val ClassType(clsId, clsTps) = getAsClassType(vtpe)
          assert(clsTps.isEmpty)
          ClassType(tc.uninitClasses.init2cd(clsId).cd.id, clsTps)
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
      case p: UninitClassDef.Parent => Seq(p.isInit, p.toInitFd, p.fromInitFd)
      case _: UninitClassDef.LeafOrIntermediate => Seq.empty
    }.toSeq
  }
  enum UninitClassDef {
    case Parent(cd_ : ClassDef, isInit: FunDef, toInitFd: FunDef, fromInitFd: FunDef, hasDescendants: Boolean)
    case LeafOrIntermediate(cd_ : ClassDef, isInitId_ : Identifier, toInitId_ : Identifier, fromInitId_ : Identifier)

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
  }
//  case class UninitClassDef(cd: ClassDef, toInit: FunDef, fromInit: FunDef)

  // TODO: Don't force OptionMut if we can avoid it
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
                val ClassType(fldCtId, fldTps) = getAsClassType(origVd.tpe)
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
        UninitClassDef.Parent(newCd, isInit = isInitFd, toInitFd = toInitFd, fromInitFd = fromInitFd, hasDescendants = !isLeaf(cls))
      } else {
        UninitClassDef.LeafOrIntermediate(newCd, isInitId_ = isInitIds(cls), toInitId_ = toInitIds(cls), fromInitId_ = fromInitIds(cls))
      }
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
                val fldClsUninit = {
                  val ClassType(fldClsId, tps) = getAsClassType(newFld.tpe)
                  if (info.nullable) {
                    assert(fldClsId == optionMutDefs.option.id && tps.size == 1)
                    val ClassType(fldClsId2, tps2) = getAsClassType(tps.head)
                    assert(tps2.isEmpty)
                    fldClsId2
                  } else {
                    assert(tps.isEmpty)
                    fldClsId
                  }
                }
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
        else {
          val allLeafs = descendantsMap(origCls).filter(isLeaf)
          val cases = allLeafs.toSeq.map { leafCls =>
            val ct = ClassType(init2uninit(leafCls), Seq.empty)
            val binder = ValDef(FreshIdentifier(leafCls.name.take(1).toLowerCase), ct)
            val nbFields = symbols.classes(leafCls).fields.size
            val pat = ClassPattern(Some(binder), ct, Seq.fill(nbFields)(WildcardPattern(None)))
            val rhs = bodyBuilder(binder.toVariable, leafCls)
            MatchCase(pat, None, rhs)
          }
          MatchExpr(thiss, cases)
        }
      }
      new FunDef(
        isInitIds(origCls),
        Seq.empty,
        Seq.empty,
        BooleanType(),
        body,
        Seq(IsMethodOf(uninitCls), Final, Derived(None), Extern) // TODO: Rm extern
      )
    }
    def mkToInitFd(origCls: Identifier): FunDef = {
      val uninitCls = init2uninit(origCls)
      new FunDef(
        toInitIds(origCls),
        Seq.empty,
        Seq.empty,
        ClassType(origCls, Seq.empty),
        NoTree(ClassType(origCls, Seq.empty)), // TODO
        Seq(IsMethodOf(uninitCls), Final, Derived(None), Extern) // TODO: Rm extern
      )
    }
    def mkFromInitFd(origCls: Identifier): FunDef = {
      val uninitCls = init2uninit(origCls)
      val fromInitVd = ValDef(FreshIdentifier("init"), ClassType(origCls, Seq.empty))
      new FunDef(
        fromInitIds(origCls),
        Seq.empty,
        Seq(fromInitVd),
        ClassType(uninitCls, Seq.empty),
        NoTree(ClassType(uninitCls, Seq.empty)), // TODO
        Seq(Derived(None))
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
    case class Env(fieldsSel: FieldsSel, bdgs: Map[Variable, ExprInfo]) {
      def resetFieldsSel: Env = Env(FieldsSel.Leaf(), bdgs)
      def ::(fld: Identifier): Env = Env(fld :: fieldsSel, bdgs)
      def +(kv: (Variable, ExprInfo)): Env = Env(fieldsSel, bdgs + kv)
    }

    var classesConsInfo: Map[Identifier, ClassConsInfo] =
      symbols.classes.map { case (clsId, cd) =>
        clsId -> ClassConsInfo(cd.fields.map(vd => vd.id -> FieldInfo(nullable = false, fullyInit = true)).toMap)
      }

    val fieldsOfClass: Map[Identifier, Identifier] = {
      symbols.classes.flatMap { case (clsId, cd) =>
        cd.fields.map(_.id -> clsId).toMap
      }
    }

    override def traverse(e: Expr, ctx: Env): Unit = {
      println(s"$e -> $ctx")
      e match {
        case NullLit() =>
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
        case v: Variable =>
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

        case ClassConstructor(ct, args) =>
          if (ct.tps.nonEmpty) {
            val allArgsInit = args.forall(exprInfoOf(_, ctx.bdgs).fullyInit)
            if (!allArgsInit) {
              throw MalformedStainlessCode(e, "Cannot have uninitialized fields for parametric classes")
            }
          }
          val cd = symbols.getClass(ct.id)
          assert(cd.fields.size == args.size)
          for ((fld, arg) <- cd.fields zip args) {
            traverse(arg, fld.id :: ctx)
          }

        case FieldAssignment(recv, selector, value) =>
          val recvInfo = exprInfoOf(recv, ctx.bdgs)
          val newFieldsSel = selector :: recvInfo.fieldsSel
          val newCtx = Env(newFieldsSel, ctx.bdgs)
          traverse(value, newCtx)

        case ClassSelector(recv, selector) =>
          traverse(recv, ctx.resetFieldsSel)

        case Let(vd, e, body) =>
          val eInfo = exprInfoOf(e, ctx.bdgs)
          traverse(e, ctx.resetFieldsSel)
          traverse(body, ctx + (vd.toVariable -> eInfo))

        case LetVar(vd, e, body) =>
          val eInfo = exprInfoOf(e, ctx.bdgs)
          traverse(e, ctx.resetFieldsSel)
          traverse(body, ctx + (vd.toVariable -> eInfo))

        case IfExpr(cond, thenn, elze) =>
          traverse(cond, ctx.resetFieldsSel)
          traverse(thenn, ctx)
          traverse(elze, ctx)

        case MatchExpr(scrutinee, cases) =>
          traverse(scrutinee, ctx.resetFieldsSel)
          for (c <- cases) {
            c.optGuard.foreach(traverse(_, ctx.resetFieldsSel))
            traverse(c.rhs, ctx)
          }

        case Block(exprs, last) =>
          exprs.foreach(traverse(_, ctx.resetFieldsSel))
          traverse(last, ctx)

        case LetRec(fds, body) =>
          fds.foreach(fd => traverse(fd.fullBody, ctx.resetFieldsSel))
          traverse(body, ctx)

        case Assert(pred, _, body) =>
          traverse(pred, ctx.resetFieldsSel)
          traverse(body, ctx)

        case Assume(pred, body) =>
          traverse(pred, ctx.resetFieldsSel)
          traverse(body, ctx)

        case Decreases(pred, body) =>
          traverse(pred, ctx.resetFieldsSel)
          traverse(body, ctx)

        case Require(pred, body) =>
          traverse(pred, ctx.resetFieldsSel)
          traverse(body, ctx)

        case Ensuring(body, pred) =>
          traverse(body, ctx)
          traverse(pred, ctx.resetFieldsSel)

        case Operator((es, _)) =>
          es.foreach(traverse(_, ctx.resetFieldsSel))
      }
    }
  }

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
        ExprInfo(FieldsSel.Leaf(), fullyInit, false) // Cannot be nullable since we are constructing a class
      case ClassSelector(recv, selector) =>
        val recRecv = exprInfoOf(recv, bdgs)
        val resFieldsSel = selector :: recRecv.fieldsSel
        // TODO: Quid utilisation pour eliminator?
        ExprInfo(selector :: recRecv.fieldsSel, recRecv.fullyInit, recRecv.nullable)
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
    val valueVd = ValDef(value, someTp, Seq.empty)
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