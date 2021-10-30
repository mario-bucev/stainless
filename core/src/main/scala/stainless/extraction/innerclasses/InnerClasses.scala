/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

/** Lift local classes (ie. class defined within a method body,
  * such as eg. anonymous classes) to the top-level.
  *
  * Turns the following program
  *
  * ```scala
  * abstract class Test[A] {
  *   def test: A
  * }
  *
  * case class TopLevel[A](topField: A) {
  *   def topMethod[B](topParam: B, x: BigInt): Test[B] {
  *      require(x != 0)
  *      val foo = 42
  *      new Test[A] {
  *        def test: A = {
  *          val b = x + foo
  *          val c = topParam
  *          this.topField
  *        }
  *      }
  *   }
  * }
  * ```
  *
  * into
  *
  * ```scala
  * abstract class Test[A] {
  *   def test: A
  * }
  *
  * case class $anon[A, B](topField: A, topParam: B, x: BigInt, foo: BigInt, outer: TopLevel[A]) {
  *   require(this.x != 0)
  *   def test: A = {
  *      val b = this.x + this.foo
  *      val c = this.topParam
  *      this.topField
  *   }
  * }
  *
  * case class TopLevel[A](topField: A) {
  *   def topMethod[B](topParam: B, x: BigInt): Test[B] {
  *      require(x != 0)
  *      val foo = 42
  *      $anon(this.topField, topParam, x, foo, this)
  *   }
  * }
  * ```
  */
class InnerClasses(override val s: Trees, override val t: methods.Trees)
                  (using override val context: inox.Context)
  extends oo.CachingPhase
     with IdentitySorts
     with oo.IdentityTypeDefs
     with oo.SimpleClasses
     with oo.SimplyCachedClasses { self =>
  import s._

  override protected def getContext(symbols: Symbols) = new TransformerContext(self.s, self.t)(using symbols)

  protected class TransformerContext(override final val s: self.s.type,
                                     override final val t: self.t.type)
                                    (using val symbols: s.Symbols)
    extends oo.ConcreteTreeTransformer(s, t) { ctx =>
    import s._
    import symbols._

    /** Represent a substitution for a lifted local class */
    case class ClassSubst(
      cd: ClassDef,               // Lifted classd
      methods: Seq[FunDef],       // Lifted methods
      typeMembers: Seq[TypeDef],  // Lifted type members
      newTypeParams: Seq[(TypeParameter, TypeParameterDef)],     // New (closed over) type params
      newParams: Seq[(Variable, ValDef)],     // New (closed over) fields
      outerRefs: Seq[ValDef],     // Outer references
      classType: ClassType        // Type of lifted class
    ) {

      def withMethods(methods: Seq[FunDef]): ClassSubst = copy(methods = methods)
      def withTypeMembers(typeMembers: Seq[TypeDef]): ClassSubst = copy(typeMembers = typeMembers)

      /** Add required type parameters to the list of explictly given ones */
      def addNewTypeParams(tps: Seq[Type], context: Context): Seq[Type] = {
        // tps ++ newTypeParams
        val scope = context.typeScope
        val realNewTyParams = newTypeParams.map((freeTyParam, _) => scope.getOrElse(freeTyParam, freeTyParam))
        tps ++ realNewTyParams
      }

      /** Add required constructor parameters to the list of explictly given ones,
        * based on the current context.
        *
        * @see [[ClassSubst#addOuterRefs]]
        * @see [[Context#toScope]]
        */
      def addNewParams(params: Seq[Expr], context: Context): Seq[Expr] = {
        val scope = context.termScope
        val realNewParams = newParams.map((freeVar, _) => scope.getOrElse(freeVar.id, freeVar))
        val realOuterRefs = context.currentClass.toSeq.flatMap(addOuterRefs)

        // TODO: What about:
        /*
        def foo(l: Int)
          class C1
            def somethign = <uses l>
          class C2
            def otherThing = <uses l>
            def m3 = new C1 <-- needs this.l (should be fine)
          class C3
            // Not using l
            def m4 = new C1 <-- we need to capture l for that
        */

        params ++ realNewParams ++ realOuterRefs
      }

      /** For each outer ref to add to a local class constructor,
        * either pass `this` or pass down the corresponding outer ref from
        * the current class.
        */
      private def addOuterRefs(currentClass: ClassDef): Seq[Expr] = {
        val thiss = This(currentClass.typed.toType)
        outerRefs map {
          case ValDef(id, ct: ClassType, _) if currentClass.id == ct.id => thiss
          case ValDef(id, _, _) => ClassSelector(thiss, id)
        }
      }
    }

    /** The context in a which a local class is defined in */
    case class Context(
      path: Path = Path.empty,                         // Current path condition
      substs: Map[Identifier, ClassSubst] = Map.empty, // Already lifted classes in scope
      currentClass: Option[ClassDef] = None,           // Enclosing class
      currentFunction: Option[FunDef] = None           // Enclosing method
    ) extends PathLike[Context] {

      // TODO: update doc: c'est free var
      /** Map each closed over field and parameters to the appropriate reference */
      def termScope: Map[Identifier, Expr] = {
        val params = for {
          fd    <- currentFunction.toSeq
          param <- fd.params
        } yield (param.id -> param.toVariable)

        val fields = for {
          cd    <- currentClass.toSeq
          subst = substs.values.find(_.cd eq cd).get // Enclosing class is already lifted, so it must be in `substs`
          (freeVar, field) <- subst.newParams
          thiss = This(ClassType(cd.id, cd.typeArgs).copiedFrom(field)).copiedFrom(field)
        } yield (freeVar.id -> ClassSelector(thiss, field.id).copiedFrom(field))

        (params ++ fields).toMap
      }

      def typeScope: Map[TypeParameter, Type] = {
        // TODO: Maybe we could get rid of currentFunction?
        val fromFn = for {
          fd     <- currentFunction.toSeq
          tparam <- fd.tparams
        } yield (tparam.tp -> tparam.tp)

        val fromClass = for {
          cd    <- currentClass.toSeq
          subst = substs.values.find(_.cd eq cd).get // Enclosing class is already lifted, so it must be in `substs`
          (freeTParam, tparamDef) <- subst.newTypeParams
        } yield (freeTParam -> tparamDef.tp)

        (fromFn ++ fromClass).toMap
      }

      /** Transform a local class type to a global one */
      def toGlobalType(tp: Type): ClassType = tp match {
        case lct: LocalClassType =>
          substs(lct.id).classType
        case ct: ClassType if substs.contains(ct.id) && ct.tps.size != substs(ct.id).cd.tparams.size =>
          val subst = substs(ct.id)
          val tps = ct.tps ++ subst.newTypeParams.map(_._2.tp)
          ClassType(ct.id, tps).copiedFrom(ct)
        case ct: ClassType =>
          ct
      }

      def merge(that: Context): Context =
        Context(
          this.path merge that.path,
          this.substs ++ that.substs,
          that.currentClass,
          that.currentFunction
        )

      def negate: Context = this.copy(path = path.negate)
      def withBinding(p: (ValDef, Expr)): Context = this.copy(path = path.withBinding(p))
      def withBound(b: ValDef): Context = this.copy(path = path.withBound(b))
      def withCond(e: Expr): Context = this.copy(path = path.withCond(e))

      def withSubst(subst: ClassSubst) = copy(substs = substs.updated(subst.cd.id, subst))
      def withSubsts(substs: Seq[ClassSubst]) = substs.foldLeft(this)(_ withSubst _)
      def withCurrentClass(cd: ClassDef) = copy(currentClass = Some(cd))
      def withCurrentFunction(fd: FunDef) = copy(currentFunction = Some(fd))
    }

    object Context extends PathProvider[Context] {
      def empty = Context()
    }

    def liftLocalClasses(fd: FunDef, ctx: Context): FunctionResult = {
      val lift = new LiftingTransformer
      val result = lift.transform(fd, ctx)
      val derived = Derived(Some(fd.id))

      val newSymbols = lift.result.values.toSeq map { subst =>
        val cd = transform(subst.cd.copy(flags = subst.cd.flags :+ derived))
        val methods = subst.methods
          .map(fd => fd.copy(flags = fd.flags :+ derived))
          .map(transform)
        val typeDefs = subst.typeMembers
          .map(td => td.copy(flags = td.flags :+ derived))
          .map(transform)

        (cd, methods, typeDefs)
      }

      (transform(result), newSymbols)
    }

    class LiftingTransformer(override val s: self.s.type, override val t: self.s.type)
                            (using override val symbols: ctx.symbols.type)
      extends imperative.TransformerWithPC {
      import s._

      def this() = this(self.s, self.s)(using ctx.symbols)

      type Env = Context
      val pp = Context

      var result: Map[Identifier, ClassSubst] = Map.empty

      def transform(cd: ClassDef, ctx: Context): t.ClassDef = {
        new ClassDef(
          transform(cd.id, ctx),
          cd.tparams.map(tdef => transform(tdef, ctx)),
          cd.parents.map(ct => transform(ct, ctx).asInstanceOf[t.ClassType]),
          cd.fields.map(vd => transform(vd, ctx)),
          cd.flags.map(f => transform(f, ctx))
        ).copiedFrom(cd)
      }

      def transform(fd: FunDef, ctx: Context): t.FunDef = {
        new FunDef(
          transform(fd.id, ctx),
          fd.tparams.map(tdef => transform(tdef, ctx)),
          fd.params.map(p => transform(p, ctx)),
          transform(fd.returnType, ctx),
          transform(fd.fullBody, ctx.withCurrentFunction(fd)),
          fd.flags.map(f => transform(f, ctx))
        ).copiedFrom(fd)
      }

      private def flattenLets(e: Expr): (Seq[LocalClassDef], Seq[LocalFunDef], Expr) = {
        def rec(e: Expr)(classes: Seq[LocalClassDef], funs: Seq[LocalFunDef]): (Seq[LocalClassDef], Seq[LocalFunDef], Expr) = {
          e match {
            case LetClass(lcds, body) => rec(body)(classes ++ lcds, funs)
            case LetRec(lfds, body) => rec(body)(classes, funs ++ lfds)
            case other => (classes, funs, other)
          }
        }

        rec(e)(Seq.empty, Seq.empty)
      }

      override def transform(e: Expr, ctx: Context): t.Expr = e match {
        case e: LetClass =>
          val (localClasses, localFunDefs, body) = flattenLets(e)
          val substs = localClasses.map(lift(_, ctx))
          val lifted = substs map { subst =>
            val methodCtx = ctx.withSubsts(substs).withCurrentClass(subst.cd)
            val lifted = subst.withMethods(subst.methods map (transform(_, methodCtx)))
            result = result.updated(lifted.cd.id, lifted)
            lifted
          }

          transform(LetRec(localFunDefs, body).copiedFrom(e), ctx withSubsts lifted)

        case LocalThis(lct) =>
          val subst = ctx.substs(lct.id)
          val ct = ClassType(lct.id, subst.addNewTypeParams(lct.tps, ctx) map (transform(_, ctx))).copiedFrom(lct)
          t.This(ct).copiedFrom(e)

        case LocalClassConstructor(lct, args) =>
          val subst = ctx.substs(lct.id)
          val ct = ClassType(lct.id, subst.addNewTypeParams(lct.tps, ctx) map (transform(_, ctx))).copiedFrom(lct)
          t.ClassConstructor(ct, subst.addNewParams(args, ctx) map (transform(_, ctx))).copiedFrom(e)

        case LocalMethodInvocation(obj, m, _, tps, args) =>
          t.MethodInvocation(transform(obj, ctx), m.id, tps map (transform(_, ctx)), args map (transform(_, ctx))).copiedFrom(e)

        case LocalClassSelector(obj, sel, _) =>
          t.ClassSelector(transform(obj, ctx), sel).copiedFrom(e)

        case _ =>
          super.transform(e, ctx)
      }

      override def transform(tp: Type, ctx: Context): t.Type = tp match {
        case lct: LocalClassType =>
          val subst = ctx.substs(lct.id)
          t.ClassType(lct.id, subst.addNewTypeParams(lct.tps, ctx) map (transform(_, ctx))).copiedFrom(tp)

        // We sometimes encounter a ClassType for a local class, which lacks the closed over type parameters.
        // eg. when we compute the parents of the lifted class in [[lift]].
        case ClassType(id, tps) if ctx.substs contains id =>
          val subst = ctx.substs(id)
          if (tps.size == subst.cd.tparams.size) t.ClassType(id, tps map (transform(_, ctx))).copiedFrom(tp)
          else t.ClassType(id, subst.addNewTypeParams(tps, ctx) map (transform(_, ctx))).copiedFrom(tp)

        case _ => super.transform(tp, ctx)
      }
    }

    /** Collect applications of local functions with a method of a local class */
    def collectFreeLocalFunsCalls(fd: FunDef): Set[ApplyLetRec] = {
      class FreeLocalFunsCollector(override val s: self.s.type, override val t: self.s.type)
        extends stainless.transformers.Transformer
           with inox.transformers.DefinitionTransformer {
        val symbols: ctx.symbols.type = ctx.symbols

        type Env = Set[Identifier]
        def initEnv = Set.empty

        var result: Set[ApplyLetRec] = Set.empty

        override def transform(e: Expr, env: Env): Expr = e match {
          case LetRec(fds, body) =>
            transform(body, env ++ fds.map(_.id).toSet)

          case app: ApplyLetRec if !env.contains(app.id) =>
            result = result + app
            super.transform(app, env)

          case _ => super.transform(e, env)
        }
      }

      val collector = new FreeLocalFunsCollector(self.s, self.s)
      collector.transform(fd)
      collector.result
    }

    /** Check validity of given lifted local class, given its methods, and the variables it closes over. */
    def checkValidLiftedClass(cd: ClassDef, methods: Seq[FunDef], freeVars: Seq[Variable]): Unit = {
      val freeFunCalls = methods flatMap collectFreeLocalFunsCalls

      freeFunCalls foreach { app =>
        throw InvalidInnerClassException(app, s"Local classes cannot close over local function definitions")
      }

      freeVars.filter(_.flags contains IsVar) foreach { v =>
        throw InvalidInnerClassException(v, s"Local classes cannot close over mutable variables")
      }
    }

    /** Current path condition expressed as a class invariant, if not trivial */
    def pathConditionToInvariant(pathCondition: Expr, lcd: LocalClassDef): Option[LocalMethodDef] = {
      pathCondition match {
        case BooleanLiteral(true) => None
        case _ => Some(LocalMethodDef(
          ast.SymbolIdentifier("inv"),
          Seq.empty,
          Seq.empty,
          BooleanType().setPos(lcd),
          pathCondition.setPos(lcd),
          Seq(IsInvariant, IsMethodOf(lcd.id))
        ).setPos(lcd))
      }
    }

    /** Convert the path condition to a (properly positioned) expression */
    def pathToClause(path: Path, lcd: LocalClassDef): Expr = {
      val pathCondition = path.toClause
      exprOps.postTraversal(_.setPos(lcd))(pathCondition)
      pathCondition
    }

    /** Lift the local class to the top, taking into account the current context and path */
    def lift(lcd: LocalClassDef, context: Context): ClassSubst = {
      val pathCondition = pathToClause(context.path, lcd)

      // Compute the variables, type parameters, and outer references being closed over by the local class.
      val freeVars       = (exprOps.freeVariablesOf(lcd) ++ exprOps.variablesOf(pathCondition)).toSeq.sortBy(_.id.name)
      val freeTypeParams = exprOps.freeTypeParamsOf(lcd).toSeq.sortBy(_.id.name)
      val enclosingRef   = context.currentClass.map(cd => This(cd.typed.toType))
      val freeOuterRefs  = (enclosingRef.toSet ++ exprOps.outerThisReferences(lcd).toSet).toSeq.sortBy(_.ct.id.name)

      // New necessary fields and type parameters
//      val newTypeParams  = freeTypeParams.map(TypeParameterDef(_))
//      val newVarFields  = freeVars.map(_.toVal)
      val newTypeParams  = freeTypeParams.map(tp => TypeParameterDef(tp.freshen))
//      val newTypeParams  = freeTypeParams.map(tp => TypeParameterDef(tp))

      class TyMap(override val s: self.s.type, override val t: self.s.type) extends ConcreteTreeTransformer(s, t) { slf =>
        override def transform(e: slf.s.Expr): slf.t.Expr = e match {
          // We need to explicitly transform LetClass to ensure we go through in each local methods
          // because the deconstructor of LetClass does not deconstruct local methods.
          case LetClass(classes, body) =>
            LetClass(classes.map(transform), transform(body))
          case e =>
            super.transform(e)
        }
        override def transform(ty: slf.s.Type): slf.t.Type = ty match {
          case t: TypeParameter if freeTypeParams.indexOf(t) >= 0 =>
            newTypeParams(freeTypeParams.indexOf(t)).tp
          case t =>
            super.transform(t)
        }
      }
      val tyMap = new TyMap(s, s)

      val newVarFields  = freeVars.map(_.toVal.freshen).map(tyMap.transform)
      val outerRefFields = freeOuterRefs.map { r =>
        ValDef(FreshIdentifier(s"outer${r.ct.id.name}"), context.toGlobalType(r.ct)).setPos(lcd.getPos)
      }.map(tyMap.transform) // TODO: should this go through transform or not?

      // Convert all parents to a ClassType
      val parents = lcd.parents.map(p => tyMap.transform(context.toGlobalType(p)).asInstanceOf[ClassType])

      // Build the new class
      val cd = new ClassDef(
        lcd.id,
        lcd.tparams ++ newTypeParams,
        parents,
        lcd.fields.map(tyMap.transform) ++ newVarFields ++ outerRefFields,
        lcd.flags
      ).copiedFrom(lcd)

      val classType = ClassType(lcd.id, cd.typeArgs)

      // Map each free variable to the corresponding field selector
      val freeVarsMap = freeVars.zip(newVarFields).map { case (v, vd) =>
        v -> ClassSelector(This(classType).copiedFrom(v), vd.id).copiedFrom(v)
      }.toMap

      // Map each outer reference to the corresponding field selector
      val freeOuterRefsMap = freeOuterRefs.zip(outerRefFields).map { case (thiss, vd) =>
        thiss.ct.id -> ClassSelector(This(classType).copiedFrom(thiss), vd.id).copiedFrom(thiss)
      }.toMap

      /** Rewrite the given method to access free variables through the new fields,
        * and to supply the proper arguments when constructing an instance of its own class.
        */
      def liftMethod(fd: LocalMethodDef): FunDef = {
        val body = exprOps.preMap {
          case v: Variable if freeVarsMap contains v =>
            Some(freeVarsMap(v))

          case a @ Assignment(v, e) if freeVarsMap contains v =>
            val ClassSelector(rec, sel) = freeVarsMap(v)
            Some(FieldAssignment(rec, sel, e).copiedFrom(a))

          case thiss: This if freeOuterRefsMap contains thiss.ct.id =>
            Some(freeOuterRefsMap(thiss.ct.id))

          case thiss: LocalThis if freeOuterRefsMap contains thiss.lct.id =>
            Some(freeOuterRefsMap(thiss.lct.id))

          case lcc @ LocalClassConstructor(lct, args) if lct.id == lcd.id =>
            val ct = ClassType(lcd.id, lct.tps ++ newTypeParams.map(_.tp))
            Some(ClassConstructor(ct, args ++ freeVars ++ freeOuterRefs).copiedFrom(lcc)) // TODO: Why freeVars ++ freeOuterRefs and not its corresponding fields???

          case _ => None
        } (fd.fullBody)

        tyMap.transform(new FunDef(fd.id, fd.tparams, fd.params, fd.returnType, body, fd.flags).copiedFrom(fd))
      }

      // Convert the current path condition to an invariant
      val localInv = pathConditionToInvariant(pathCondition, lcd)
      val methods = (localInv.toSeq ++ lcd.methods) map liftMethod
      val typeMembers = lcd.typeMembers map (_.toTypeDef) map (tyMap.transform)

      checkValidLiftedClass(cd, methods, freeVars)

      ClassSubst(
        cd,
        methods,
        typeMembers,
//        freeTypeParams,
//        freeVars.map(_.toVal),
//        newTypeParams.map(_.tp),
        freeTypeParams zip newTypeParams,
        freeVars zip newVarFields,
        outerRefFields,
        classType
      )
    }
  }

  override protected type FunctionResult = (t.FunDef, Seq[(t.ClassDef, Seq[t.FunDef], Seq[t.TypeDef])])

  override protected val funCache: SimpleCache[s.FunDef, FunctionResult] = new SimpleCache[s.FunDef, FunctionResult]

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): FunctionResult = {
    import context.{given, _}

    val optClass = fd.flags.collectFirst { case IsMethodOf(cid) => symbols.classes(cid) }
    liftLocalClasses(fd, Context(currentClass = optClass, currentFunction = Some(fd)))
  }

  override protected def registerFunctions(symbols: t.Symbols, results: Seq[FunctionResult]): t.Symbols = {
    val (functions, locals) = results.unzip
    val (localClasses, localMethods, localTypeDefs) = locals.flatten.unzip3
    symbols
      .withClasses(localClasses)
      .withTypeDefs(localTypeDefs.flatten)
      .withFunctions(functions ++ localMethods.flatten)
    /*
    extension [A, B, C, D](s: Seq[(A, B, C, D)]) {
      def unzip4: (Seq[A], Seq[B], Seq[C], Seq[D]) = (s.map(_._1), s.map(_._2), s.map(_._3), s.map(_._4))
    }

    def freshenClasses(enclosingFn: t.FunDef, locals: Seq[(t.ClassDef, Seq[t.FunDef], Seq[t.TypeDef])]): (t.FunDef, Seq[t.ClassDef], Seq[t.FunDef], Seq[t.TypeDef]) = {
      val allCDs = locals.map(_._1)
      val allMeths = locals.flatMap(_._2)
      val allTDs = locals.flatMap(_._3)
      allCDs.foldLeft((enclosingFn, Seq.empty[t.ClassDef], allMeths, allTDs)) {
        case ((enclosingFnAcc, cdsAcc, methsAcc, tdsAcc), cd) =>
          val (newEnclosingFn, newCd, newMeths, newTds) = t.exprOps.freshenClass(enclosingFnAcc, cd, methsAcc, tdsAcc)
          (newEnclosingFn, cdsAcc :+ newCd, newMeths, newTds)
      }
    }

    val owo = results.find(_._1.id.toString == "foo")
    val (functions, localClasses0, localMethods0, localTypeDefs0) = results.map(freshenClasses.tupled).unzip4
    val localClasses = localClasses0.flatten
    val localMethods = localMethods0.flatten
    val localTypeDefs = localTypeDefs0.flatten
    symbols
      .withClasses(localClasses)
      .withTypeDefs(localTypeDefs)
      .withFunctions(functions ++ localMethods)
    */
    /*
//    val (functions, locals) = results.unzip

//    val (localClasses, localMethods, localTypeDefs) = locals.flatten.unzip3
    val wot = results.find(_._1.id.toString == "foo")

//    val (localClasses, localMethods, localTypeDefs) = locals.flatten.map {
//      case (cd, methods, typeDefs) => t.exprOps.freshenClass(cd, methods, typeDefs)
//    }.unzip3

//    val (freshendLocalClasses, freshendLocalMethods, freshendLocalTypeDefs) = locals.flatten.map {
//      case (cd, methods, typeDefs) => t.exprOps.freshenClass(cd, methods, typeDefs)
//    }.unzip3
    // type FunctionResult = (t.FunDef, Seq[(t.ClassDef, Seq[t.FunDef], Seq[t.TypeDef])])
    val (functions, freshenedLocals) = results.map {
      case (enclosingFn, locals) =>
        t.exprOps.freshenClasses(enclosingFn, locals)
    }.unzip
    val (localClasses, localMethods, localTypeDefs) = freshenedLocals.flatten.unzip3
    val owo = fns.find(_.id.toString == "foo")
    */
/*
    val (functions, locals) = results.unzip
    val (localClasses, localMethods, localTypeDefs) = locals.flatten.map {
      case (cd, methods, typeDefs) =>
        val (_, a, b, c) = t.exprOps.freshenClass(functions.head, cd, methods, typeDefs)
        (a, b, c)
    }.unzip3
*/
    /*
    symbols
      .withClasses(localClasses)
      .withTypeDefs(localTypeDefs.flatten)
      .withFunctions(functions ++ localMethods.flatten)
    */
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): t.ClassDef = {
    import context.{given, _}
    context.transform((new LiftingTransformer).transform(cd, Context.empty))
  }
}

object InnerClasses {
  def apply(ts: Trees, tt: methods.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends InnerClasses(s, t)
    new Impl(ts, tt)
  }
}
