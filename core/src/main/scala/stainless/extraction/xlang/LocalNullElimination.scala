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

    val uninitClasses = createUninitClasses(symbols, optMutDefs, uninitCC.classesNullableSelections)

    /*
    println(uninitClasses.init2cd.mkString("\n"))
    println("===========================================")
    println("===========================================")
    */
    TransformerContext(symbols, optMutDefs, uninitCC.classesNullableSelections, uninitClasses)
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (t.FunDef, Unit) = {
    val transformer = new Eliminator(context)
    val newBody = transformer.transform(fd.fullBody, transformer.Env.empty)
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

    given Symbols = tc.symbols

    private val fieldsOfClass: Map[Identifier, Identifier] = {
      tc.symbols.classes.flatMap { case (clsId, cd) =>
        cd.fields.map(_.id -> clsId).toMap
      }
    }

    case class Env(ctxKind: CtxKind, bdgs: Map[Variable, BdgInfo]) {
      def withPureCtx: Env = Env(CtxKind.Pure, bdgs)

      def nullableSelsOrEmpty: NullableSelections = ctxKind match {
        case CtxKind.Impure(nullableSelections, _) => nullableSelections
        case CtxKind.Pure => NullableSelections.empty
      }
    }
    object Env {
      def empty: Env = Env(CtxKind.Pure, Map.empty) // TODO: Et si returned expr est "impure" mais qu'il faut la transformer en "pure"???
    }
    case class BdgInfo(nullableSelections: NullableSelections, newTpe: Type)
    enum CtxKind {
      case Impure(nullableSels: NullableSelections, expectedType: Type)
      case Pure
    }

    private def toUninitType(tpe: Type): Type = {
      tpe match {
        case ClassType(clsId, clsTps) =>
          assert(clsTps.isEmpty)
          val uninitCd = tc.uninitClasses.init2cd(clsId)
          ClassType(uninitCd.cd.id, Seq.empty)
        // TODO: Also support for nested array, etc.
        case ArrayType(ClassType(clsId, clsTps)) =>
          assert(clsTps.isEmpty)
          val uninitCd = tc.uninitClasses.init2cd(clsId)
          ArrayType(ClassType(uninitCd.cd.id, Seq.empty))
        case _ => sys.error(s"Unsupported: $tpe")
      }
    }

    // TODO: Expliquer pk ce eOrigTpe
    private def adaptExpression(e: Expr, eOrigTpe: Type, eUninit: Boolean, eNullable: Boolean,
                                resUninit: Boolean, resNullable: Boolean): Expr = {
      if (resUninit == !eUninit) {
        val e1 = {
          if (eNullable) get(e).copiedFrom(e)
          else e
        }
        val (e2, tpe2) = eOrigTpe match {
          case ClassType(clsId, clsTps) =>
            assert(clsTps.isEmpty)
            val uninitCd = tc.uninitClasses.init2cd(clsId)
            if (resUninit) {
              (FunctionInvocation(uninitCd.fromInitId, Seq.empty, Seq(e1)).copiedFrom(e), ClassType(uninitCd.cd.id, Seq.empty))
            } else {
              (MethodInvocation(e1, uninitCd.toInitId, Seq.empty, Seq.empty).copiedFrom(e), ClassType(clsId, Seq.empty))
            }
          // TODO: Also support for nested array, etc.
          case ArrayType(ClassType(clsId, clsTps)) =>
            assert(clsTps.isEmpty)
            val uninitCd = tc.uninitClasses.init2cd(clsId)
            if (resUninit) {
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
          else {
            val tpe = if (eUninit) toUninitType(eOrigTpe) else eOrigTpe
            some(e, tpe).copiedFrom(e)
          }
        } else e
      }
    }

    private def widenedNullable(ns: NullableSelections): NullableSelections = {
      // TODO: Inefficient if there are multiple times the same field appearing...
      NullableSelections(Selections(ns.sels.sels.flatMap { ps =>
        val ixFirstField = ps.path.indexWhere(_.isField)
        if (ixFirstField < 0) Set(ps)
        else {
          val (prefix, rest) = ps.path.splitAt(ixFirstField)
          val Selection.Field(fld) = ps.path(ixFirstField): @unchecked
          val cls = fieldsOfClass(fld)
          val clsNullableSels = tc.classesNullableSelections(cls)
          // TODO: What about the siblings or descendants???
          assert(clsNullableSels.existsPrefix(PathSelection(rest)))
          clsNullableSels.sels.sels
        }
      }))
    }

    private def widenedNullableSelection(e: Expr, env: Env): NullableSelections =
      widenedNullable(nullableSelections(e, env.bdgs.view.mapValues(_.nullableSelections).toMap))

    override def transform(e: Expr, env: Env): Expr = {
      e match {
        case NullLit() =>
          env.ctxKind match {
            case CtxKind.Impure(nullableSels, expectedType) =>
              assert(nullableSels.isNullable)
              val ClassType(id, tps) = getAsClassType(expectedType)
              assert(id == tc.optionMutDefs.option.id && tps.size == 1)
              none(tps.head).copiedFrom(e)
            case CtxKind.Pure =>
              throw MalformedStainlessCode(e, "Unsupported usage of `null` (pure context)")
          }
        case v: Variable =>
          val resUninit = env.nullableSelsOrEmpty.isUninit
          val resNullable = env.nullableSelsOrEmpty.isNullable
          env.bdgs.get(v) match {
            case Some(BdgInfo(vNullableSels, newTpe)) =>
              val v2 = v.copy(tpe = newTpe)
              adaptExpression(v2, v.tpe, eUninit = vNullableSels.isUninit, eNullable = vNullableSels.isNullable, resUninit, resNullable)
            case None =>
              adaptExpression(v, v.tpe, eUninit = false, eNullable = false, resUninit, resNullable)
          }

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
          assert(env.nullableSelsOrEmpty.hasNoArrayStart)
          val fieldsOrig = tc.symbols.getClass(ct.id).fields
          assert(fieldsOrig.size == args.size)
          val recArgs = fieldsOrig.zip(args).zipWithIndex.map { case ((fld, arg), ix) =>
            val newEnv = env.ctxKind match {
              case CtxKind.Pure => env
              case CtxKind.Impure(nullableSels, _) =>
                val fldNullableSels = nullableSels.filter(fld.id)
                if (fldNullableSels.isEmpty) env.withPureCtx
                else {
                  val expectedTpe = tc.uninitClasses.init2cd(ct.id).cd.fields(ix).tpe
                  env.copy(ctxKind = CtxKind.Impure(fldNullableSels, expectedTpe))
                }
            }
            transform(arg, newEnv)
          }
          val useUninit = env.nullableSelsOrEmpty.isUninit
          val (newExpr, newTpe) = {
            if (useUninit) {
              assert(ct.tps.isEmpty)
              val newCt = ClassType(tc.uninitClasses.init2cd(ct.id).cd.id, Seq.empty)
              (ClassConstructor(newCt, recArgs), newCt)
            } else (ClassConstructor(ct, recArgs), ct)
          }
          if (env.nullableSelsOrEmpty.isNullable) some(newExpr, newTpe)
          else newExpr

        case ClassSelector(recv, selector) =>
          val origCls = fieldsOfClass(selector)
          val origCd = tc.symbols.getClass(origCls)
          val origTpe = e.getType
          val recvNullableSels = widenedNullableSelection(recv, env)
          val (recvCtx, newSelector, newTpe) = {
            if (recvNullableSels.isEmpty) (CtxKind.Pure, selector, origTpe)
            else {
              val uninitCls = tc.uninitClasses.init2cd(origCls).cd.id
              val newSelector = tc.uninitClasses.fieldOfUninit(origCls, selector)
              (CtxKind.Impure(recvNullableSels.withoutNullable, ClassType(uninitCls, Seq.empty)), newSelector.id, newSelector.tpe)
            }
          }
          val selNullableSels = recvNullableSels.filter(selector)
          val recvRec = transform(recv, env.copy(ctxKind = recvCtx))
          val newExpr = ClassSelector(recvRec, newSelector).copiedFrom(e)
          adaptExpression(newExpr, origTpe,
            eUninit = selNullableSels.isUninit, eNullable = selNullableSels.isNullable,
            resUninit = env.nullableSelsOrEmpty.isUninit, resNullable = env.nullableSelsOrEmpty.isNullable)

        case Assignment(v, value) =>
          val (ctxKind, newTpe) = env.bdgs.get(v) match {
            case Some(BdgInfo(nullableSelections, newTpe)) if !nullableSelections.isEmpty =>
              (CtxKind.Impure(nullableSelections, newTpe), newTpe)
            case _ => (CtxKind.Pure, v.tpe)
          }
          val valueRec = transform(value, env.copy(ctxKind = ctxKind))
          Assignment(v.copy(tpe = newTpe), valueRec).copiedFrom(e)

        case fa @ FieldAssignment(recv, selector, value) =>
          val origCls = fieldsOfClass(selector)
          val recvNullableSels = widenedNullableSelection(recv, env)
          val (recvCtx, newSelector) = {
            if (recvNullableSels.isEmpty) (CtxKind.Pure, selector)
            else {
              val uninitCls = tc.uninitClasses.init2cd(origCls).cd.id
              val newSelector = tc.uninitClasses.fieldOfUninit(origCls, selector).id
              (CtxKind.Impure(recvNullableSels.withoutNullable, ClassType(uninitCls, Seq.empty)), newSelector)
            }
          }
          val recvRec = transform(recv, env.copy(ctxKind = recvCtx))
          val valCtx = {
            val selNullableSels = recvNullableSels.filter(selector)
            if (selNullableSels.isEmpty) CtxKind.Pure
            else {
              val uninitFld = tc.uninitClasses.fieldOfUninit(origCls, selector)
              CtxKind.Impure(selNullableSels, uninitFld.tpe)
            }
          }
          val valRec = transform(value, env.copy(ctxKind = valCtx))
          FieldAssignment(recvRec, newSelector, valRec)

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
          assert(widenedNullableSelection(e, env).isEmpty)
          // TODO: What if there is a null in e? This will return a NothingType!
          val eTpe = e.getType
          val esRec = es.map(transform(_, env.withPureCtx))
          val newE = recons(esRec).copiedFrom(e)
          env.ctxKind match {
            case CtxKind.Pure => newE
            case CtxKind.Impure(nullableSels, _) =>
              adaptExpression(newE, eTpe, eUninit = false, eNullable = false, nullableSels.isUninit, nullableSels.isNullable)
          }
      }
    }

    def optionTpe(tpe: Type): Type = ClassType(tc.optionMutDefs.option.id, Seq(tpe))
    def none(tpe: Type): Expr = ClassConstructor(ClassType(tc.optionMutDefs.none.id, Seq(tpe)), Seq.empty)
    def some(e: Expr, tpe: Type): Expr = ClassConstructor(ClassType(tc.optionMutDefs.some.id, Seq(tpe)), Seq(e)).copiedFrom(e)
    def get(e: Expr): Expr = MethodInvocation(e, tc.optionMutDefs.get.id, Seq.empty, Seq.empty).copiedFrom(e)

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
      // Note: if we declare a var set to null for a class known for having uninit fields,
      // we cannot know by just looking at the null whether we should go for the uninit construction
      // or the original one (both cases wrapped in an OptionMut of course)
      // Therefore, we look at the assignment usage to determine the usage
      // TODO: Do it
      // TODO: What about aliasing, field/array assignment and so on?
      val eNullableSels = widenedNullableSelection(e, env)
      val (eCtx, eNewTpe) = {
        if (eNullableSels.isEmpty) (CtxKind.Pure, vd.tpe)
        else {
          val eNewTpe1 = if (eNullableSels.isUninit) toUninitType(vd.tpe) else vd.tpe
          val eNewTpe2 = if (eNullableSels.isNullable) optionTpe(eNewTpe1) else eNewTpe1
          (CtxKind.Impure(eNullableSels, eNewTpe2), eNewTpe2)
        }
      }
      val eRec = transform(e, env.copy(ctxKind = eCtx))
      val bodyEnv = env.copy(bdgs = env.bdgs + (vd.toVariable -> BdgInfo(eNullableSels, eNewTpe)))
      val bodyRec = transform(body, bodyEnv)
      mkLet(vd.copy(tpe = eNewTpe), eRec, bodyRec).copiedFrom(e)
    }
  }

  case class UninitClassDefs(init2cd: Map[Identifier, UninitClassDef],
                             uninit2init: Map[Identifier, Identifier]) {
    def allNewClasses: Seq[ClassDef] = init2cd.values.map(_.cd).toSeq
    def allNewFunctions: Seq[FunDef] = init2cd.values.flatMap {
      case p: UninitClassDef.Parent => Seq(p.isInit, p.toInitFd, p.fromInitFd, p.isInitArr, p.toInitArrFd, p.fromInitArrFd)
      case _: UninitClassDef.LeafOrIntermediate => Seq.empty
    }.toSeq
    def fieldOfUninit(origCls: Identifier, origFld: Identifier)(using symbols: Symbols): ValDef = {
      val ix = symbols.classes(origCls).fields.indexWhere(_.id == origFld)
      init2cd(origCls).cd.fields(ix)
    }
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
                                  classesNullableSelections: Map[Identifier, NullableSelections]): UninitClassDefs = {
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

    val initNeedUninit = classesNullableSelections.filter(_._2.isUninit).keySet
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
        val allNullableSels = classesNullableSelections(cls)
        origCD.fields.map { origVd =>
          val fldNullableSels = allNullableSels.filter(origVd.id)

          if (!fldNullableSels.isNullable && !fldNullableSels.isUninit) {
            ValDef(origVd.id.freshen, origVd.tpe, origVd.flags)
          } else {
            val tpe2 = {
              if (fldNullableSels.isUninit) {
                val ClassType(fldCtId, fldTps) = getAsClassType(origVd.tpe) // TODO: Non, il peut y avoir des array ici
                assert(init2uninit.contains(fldCtId))
                ClassType(init2uninit(fldCtId), fldTps)
              } else origVd.tpe
            }
            val tpe3 = {
              if (fldNullableSels.isNullable) {
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

    def getUnderlyingUninitIdOf(fldNullableSels: NullableSelections, newFld: ValDef): Identifier = {
      val ClassType(fldClsId, tps) = getAsClassType(newFld.tpe) // TODO: Non, array
      if (fldNullableSels.isNullable) {
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
        val allNullableSels = classesNullableSelections(origCls)
        val origField = classes(origCls).fields
        val uninitCls = init2uninit(origCls)

        val conjs = origField.zipWithIndex
          .flatMap { case (origFld, fldIx) =>
            val fldNullableSels = allNullableSels.filter(origFld.id)
            if (!fldNullableSels.isNullable && !fldNullableSels.isUninit) {
              Seq.empty[Expr]
            } else {
              val newFld = newFieldsMap(origCls)(fldIx)
              val sel = ClassSelector(recv, newFld.id)
              val isDefined = {
                if (fldNullableSels.isNullable) Seq(MethodInvocation(sel, optionMutDefs.isDefined.id, Seq.empty, Seq.empty))
                else Seq.empty[Expr]
              }
              val fldGet = {
                if (fldNullableSels.isNullable) MethodInvocation(sel, optionMutDefs.get.id, Seq.empty, Seq.empty)
                else sel
              }
              val isInit = {
                if (fldNullableSels.isUninit) {
                  val fldClsUninit = getUnderlyingUninitIdOf(fldNullableSels, newFld)
                  val fldClsInit = uninit2init(fldClsUninit)
                  Seq(MethodInvocation(fldGet, isInitIds(fldClsInit), Seq.empty, Seq.empty))
                } else Seq.empty[Expr]
              }
              isDefined ++ isInit
            }
          }
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
        val allNullableSels = classesNullableSelections(origCls)
        val origFields = classes(origCls).fields
        val uninitCls = init2uninit(origCls)
        val args = origFields.zipWithIndex.map { case (origField, fldIx) =>
          val newFld = newFieldsMap(origCls)(fldIx)
          val sel = FreshCopy(ClassSelector(recv, newFld.id)) // TODO: !!!! NEED CHECKS TO ENSURE NO MUTATION
          val fldNullableSel = allNullableSels.filter(origField.id)
          val get = {
            if (fldNullableSel.isNullable) MethodInvocation(sel, optionMutDefs.get.id, Seq.empty, Seq.empty)
            else sel
          }
          if (fldNullableSel.isUninit) {
            val fldClsUninit = getUnderlyingUninitIdOf(fldNullableSel, newFld)
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
        val allNullableSels = classesNullableSelections(origCls)
        val origFields = classes(origCls).fields
        val uninitCls = init2uninit(origCls)
        val args = origFields.zipWithIndex.map { case (origField, fldIx) =>
          val newFld = newFieldsMap(origCls)(fldIx)
          val sel = FreshCopy(ClassSelector(recv, origField.id)) // TODO: !!!! NEED CHECKS TO ENSURE NO MUTATION
          val fldNullableSel = allNullableSels.filter(origField.id)
          val fromInit = {
            if (fldNullableSel.isUninit) {
              val fldClsUninit = getUnderlyingUninitIdOf(fldNullableSel, newFld)
              val fldClsInit = uninit2init(fldClsUninit)
              FunctionInvocation(fromInitIds(fldClsInit), Seq.empty, Seq(sel))
            }
            else sel
          }
          if (fldNullableSel.isNullable) {
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

  private class UninitClassesCollector(using symbols: Symbols) extends inox.transformers.Traverser {
    override val trees: s.type = s
    case class Env(currSels: Selections,
                   bdgsSels: Map[Variable, Selections],
                   bdgsNullable: Map[Variable, NullableSelections]) {
      // We use withEmptyPath and not empty because adding selections to "empty" does not do anything
      def resetSelectionCtx: Env = copy(currSels = Selections.withEmptyPath)

      def :+(fld: Identifier): Env = copy(currSels = currSels :+ fld)

      def :+(sel: Selection): Env = copy(currSels = currSels :+ sel)

      def +(kv: (Variable, (Selections, NullableSelections))): Env =
        Env(currSels, bdgsSels + (kv._1 -> kv._2._1), bdgsNullable + (kv._1 -> kv._2._2))
    }
    object Env {
      def init: Env = Env(Selections.withEmptyPath, Map.empty, Map.empty)
    }

    var classesNullableSelections: Map[Identifier, NullableSelections] =
      symbols.classes.keySet.map(_ -> NullableSelections.empty).toMap

    private def updateNullable(sels: Selections): Unit = {
      val selsPerField = sels.groupByField
      for ((_, cd) <- symbols.classes) {
        val currNullable = classesNullableSelections(cd.id)
        val newNullable = cd.fields.foldLeft(currNullable) {
          case (acc, fld) =>
            val fldSels = selsPerField.get(fld.id).map(fld.id :: _).getOrElse(Selections.empty)
            acc union NullableSelections(fldSels)
        }
        classesNullableSelections = classesNullableSelections.updated(cd.id, newNullable)
      }
    }

    override def traverse(e: Expr, ctx: Env): Unit = {
//      println(s"$e -> $ctx")
      e match {
        case NullLit() =>
          updateNullable(ctx.currSels)

        case v: Variable =>
          ctx.bdgsNullable.get(v) match {
            case Some(nullable) => updateNullable(ctx.currSels append nullable.sels)
            case None => ()
          }

        case ClassConstructor(ct, args) =>
          if (ct.tps.nonEmpty) {
            val argsNullable = args.foldLeft(NullableSelections.empty)(_ union nullableSelections(_, ctx.bdgsNullable))
            if (argsNullable.isNullable || argsNullable.isUninit) {
              throw MalformedStainlessCode(e, "Cannot have uninitialized or nullable fields for parametric classes")
            }
          }
          val cd = symbols.getClass(ct.id)
          assert(cd.fields.size == args.size)
          for ((fld, arg) <- cd.fields zip args) {
            traverse(arg, ctx :+ fld.id)
          }

        case FieldAssignment(recv, selector, value) =>
          traverse(recv, ctx.resetSelectionCtx)
          val recvSels = activeSelections(recv, ctx.bdgsSels)
          traverse(value, ctx.copy(currSels = recvSels :+ selector))

        case ClassSelector(recv, selector) =>
          traverse(recv, ctx.resetSelectionCtx)

        // TODO: ArrayUpdateD ?
        case FiniteArray(elems, _) =>
          for (elem <- elems) {
            traverse(elem, ctx :+ Selection.Array)
          }

        case LargeArray(elems, default, sze, _) =>
          assert(elems.isEmpty, "What, this elems is actually populated with something???")
          traverse(sze, ctx.resetSelectionCtx)
          traverse(default, ctx :+ Selection.Array)

        case ArraySelect(arr, ix) =>
          traverse(arr, ctx.resetSelectionCtx)
          traverse(ix, ctx.resetSelectionCtx)

        case ArrayUpdate(arr, ix, value) =>
          traverse(arr, ctx.resetSelectionCtx)
          traverse(ix, ctx.resetSelectionCtx)
          val arrSels = activeSelections(arr, ctx.bdgsSels)
          traverse(value, ctx.copy(currSels = arrSels :+ Selection.Array))

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

  enum Selection {
    case Field(id: Identifier)
    case Array

    def isField: Boolean = this match {
      case Field(_) => true
      case _ => false
    }
    def isArray: Boolean = this match {
      case Array => true
      case _ => false
    }
  }

  case class PathSelection(path: Seq[Selection]) {
    def :+(sel: Selection): PathSelection = PathSelection(path :+ sel)

    def :+(fld: Identifier): PathSelection = this :+ Selection.Field(fld)

    def ++(other: PathSelection): PathSelection = PathSelection(path ++ other.path)

    def ::(fld: Identifier): PathSelection = Selection.Field(fld) :: this

    def ::(sel: Selection): PathSelection = PathSelection(sel +: path)

    def isPrefixOf(other: PathSelection): Boolean = other.path.indexOfSlice(this.path) == 0

    def isSuffixOf(other: PathSelection): Boolean = {
      this.path.isEmpty || {
        val ix = other.path.indexOfSlice(this.path)
        ix >= 0 && ix == other.path.length - this.path.length
      }
    }
  }
  object PathSelection {
    def empty: PathSelection = PathSelection(Seq.empty)
  }

  case class Selections(sels: Set[PathSelection]) {
    require(Selections.headInvariant(sels))
    require(Selections.fieldInvariant(sels))

    def isEmpty: Boolean = sels.isEmpty

    def containsEmptyPath: Boolean = sels(PathSelection.empty)

    def containsNonEmptyPath: Boolean = Selections.containsNonEmptyPath(sels)

    def union(other: Selections): Selections = Selections(sels union other.sels)

    def ::(sel: Selection): Selections = Selections(sels.map(sel :: _))

    def ::(fld: Identifier): Selections = Selection.Field(fld) :: this

    def :::(prefix: PathSelection): Selections = Selections(sels.map(prefix ++ _))

    def :+(sel: Selection): Selections = Selections(sels.map(_ :+ sel))

    def :+(fld: Identifier): Selections = this :+ Selection.Field(fld)

    def append(other: Selections): Selections = Selections(sels.flatMap(ps => other.sels.map(ps ++ _)))

    def filter(prefix: Selection): Selections = Selections(sels.flatMap { ps =>
      // TODO: What if ps.path is empty? Should we include it or not?
      if (ps.path.nonEmpty && ps.path.head == prefix) Some(PathSelection(ps.path.tail))
      else None
    })

    def existsPrefix(prefix: PathSelection): Boolean = sels.exists(prefix.isPrefixOf)

    def existsSuffix(suffix: PathSelection): Boolean = sels.exists(suffix.isSuffixOf)

    def isSuffixIn(bigger: Selections): Boolean = sels.forall(bigger.existsSuffix)

    def groupByField: Map[Identifier, Selections] = Selections.groupByField(sels).view.mapValues(Selections.apply).toMap

    def hasNoArrayStart: Boolean = Selections.hasNoArrayStart(sels)

    def hasNoFieldStart: Boolean = Selections.hasNoFieldStart(sels)

//    def withArrayStartStripped: Selections = Selections(sels.flatMap { ps =>
//      if (ps.path.isEmpty) Some(ps)
//      else ps.path.head match {
//        case Selection.Field(ps) =>
//      }
//    })
  }
  object Selections {
    def empty: Selections = Selections(Set.empty)
    def withEmptyPath: Selections = Selections(Set(PathSelection.empty))

    private def containsNonEmptyPath(sels: Set[PathSelection]): Boolean = sels.exists(_.path.nonEmpty)

    private def hasNoArrayStart(sels: Set[PathSelection]): Boolean = sels.forall(ps => ps.path.isEmpty || !ps.path.head.isArray)

    private def hasNoFieldStart(sels: Set[PathSelection]): Boolean = sels.forall(ps => ps.path.isEmpty || !ps.path.head.isField)

    private def headInvariant(sels: Set[PathSelection]): Boolean =
      !containsNonEmptyPath(sels) || (hasNoArrayStart(sels) == !hasNoFieldStart(sels))

    private def fieldInvariant(sels: Set[PathSelection]): Boolean =
      groupByField(sels).values.forall(headInvariant)

    private def groupByField(sels: Set[PathSelection]): Map[Identifier, Set[PathSelection]] = {
      type FldMap = Map[Identifier, Set[PathSelection]]

      def add(m: FldMap, fld: Identifier, pss: Set[PathSelection]): FldMap =
        m.updatedWith(fld)(_.map(_ union pss).orElse(Some(pss)))

      def combine(m1: FldMap, m2: FldMap): FldMap = {
        (m1.keySet ++ m2.keySet).foldLeft(Map.empty : FldMap) {
          case (acc, fld) =>
            acc + (fld -> (m1.getOrElse(fld, Set.empty) union m2.getOrElse(fld, Set.empty)))
        }
      }

      def group(ps: PathSelection): FldMap = {
        ps.path.indices.foldLeft(Map.empty : FldMap) {
          case (acc, i) =>
            ps.path(i) match {
              case Selection.Field(fld) =>
                val rest = PathSelection(ps.path.drop(i + 1))
                add(acc, fld, Set(rest))
              case Selection.Array => acc
            }
        }
      }
      sels.foldLeft(Map.empty : FldMap) {
        case (acc, ps) => combine(acc, group(ps))
      }
    }
  }

  case class NullableSelections(sels: Selections) {
    def isEmpty: Boolean = sels.isEmpty

    def isNullable: Boolean = sels.containsEmptyPath

    def isUninit: Boolean = sels.containsNonEmptyPath

    def union(other: NullableSelections): NullableSelections = NullableSelections(sels union other.sels)

    def ::(fld: Identifier): NullableSelections = NullableSelections(fld :: sels)

    def ::(sel: Selection): NullableSelections = NullableSelections(sel :: sels)

    def :::(prefix: PathSelection): NullableSelections = NullableSelections(prefix ::: sels)

    def existsPrefix(prefix: PathSelection): Boolean = sels.existsPrefix(prefix)

    def hasNoArrayStart: Boolean = sels.hasNoArrayStart

    def hasNoFieldStart: Boolean = sels.hasNoFieldStart

    def isSuffixIn(bigger: NullableSelections): Boolean = sels.isSuffixIn(bigger.sels)

    // TODO: What if recv itself is nullable?
    def filter(prefix: Selection): NullableSelections = NullableSelections(sels filter prefix)

    def filter(prefix: Identifier): NullableSelections = this filter Selection.Field(prefix)

    def withoutNullable: NullableSelections = NullableSelections(Selections(sels.sels - PathSelection.empty))
  }
  object NullableSelections {
    def empty: NullableSelections = NullableSelections(Selections.empty)
    def nullable: NullableSelections = NullableSelections(Selections.withEmptyPath)
  }

  private def nullableSelections(e: Expr, bdgs: Map[Variable, NullableSelections])(using symbols: Symbols): NullableSelections = {
    def go(e: Expr, bdgs: Map[Variable, NullableSelections]): NullableSelections = e match {
      case NullLit() =>
        NullableSelections.nullable
      case v: Variable =>
        bdgs.getOrElse(v, NullableSelections.empty)
      case ClassConstructor(ct, args) =>
        val fields = symbols.getClass(ct.id).fields
        assert(args.size == fields.size)
        fields.zip(args).foldLeft(NullableSelections.empty) {
          case (acc, (field, arg)) =>
            acc union (field.id :: go(arg, bdgs))
        }
      // TODO: ArrayUpdateD ?
      case FiniteArray(elems, _) =>
        elems.foldLeft(NullableSelections.empty) {
          case (acc, elem) =>
            acc union (Selection.Array :: go(elem, bdgs))
        }
      case LargeArray(elems, default, _, _) =>
        assert(elems.isEmpty, "What, this elems is actually populated with something???")
        Selection.Array :: go(default, bdgs)
      case ClassSelector(recv, sel) =>
        // TODO: What if recv itself is nullable?
        go(recv, bdgs).filter(sel)
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
        go(thenn, bdgs) union go(elze, bdgs)
      case MatchExpr(_, cases) =>
        cases.foldLeft(NullableSelections.empty) {
          case (acc, cse) =>
            acc union go(cse.rhs, bdgs)
        }
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

  private def activeSelections(e: Expr, bdgs: Map[Variable, Selections]): Selections = {
    // Note: we use withEmptyPath because adding Selection to "empty" still results in empty

    def goBranches(branches: Seq[Expr], bdgs: Map[Variable, Selections]): Selections =
      branches.foldLeft(Selections.withEmptyPath)(_ union go(_, bdgs))

    def go(e: Expr, bdgs: Map[Variable, Selections]): Selections = e match {
      case v: Variable =>
        bdgs.getOrElse(v, Selections.withEmptyPath)
      case ArraySelect(arr, _) =>
        go(arr, bdgs) :+ Selection.Array
      case ClassSelector(recv, selector) =>
        go(recv, bdgs) :+ selector
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
      case _ => Selections.withEmptyPath
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