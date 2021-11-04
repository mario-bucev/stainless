/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc.*
import dotty.tools.dotc.transform.SymUtils.*
import ast.tpd
import ast.untpd
import ast.Trees.*
import core.Contexts
import core.Contexts.Context as DottyContext
import core.Names.*
import core.StdNames.*
import core.Symbols.*
import core.Types.*
import core.Flags.*
import core.NameKinds
import common.ClassDefs
import util.{NoSourcePosition, SourcePosition}
import stainless.ast.SymbolIdentifier
import extraction.xlang.trees as xt

import scala.collection.mutable.Map as MutableMap
import scala.collection.immutable.ListMap
import scala.language.implicitConversions

class CodeExtraction(inoxCtx: inox.Context, cache: SymbolsContext)(using override val dottyCtx: DottyContext)
  extends ASTExtractors {

  import AuxiliaryExtractors._
  import ExpressionExtractors._
  import StructuralExtractors._

  lazy val reporter = inoxCtx.reporter

  given givenDebugSection: inox.DebugSection = frontend.DebugSectionExtraction

  // TODO: no equivalent in Scalac; seems also error-prone (in extractClass, getIdentifier is used whereas field fetching uses getParam...)
  // private def getParam(sym: Symbol): SymbolIdentifier = cache fetchParam sym

  private def getIdentifier(sym: Symbol): SymbolIdentifier = cache fetch sym

  private def annotationsOf(sym: Symbol, ignoreOwner: Boolean = false): Seq[xt.Flag] = {
    getAnnotations(sym, ignoreOwner = ignoreOwner)
      .filter { case (name, _) => !name.startsWith("isabelle") }
      .map { case (name, args) =>
        xt.extractFlag(name, args.map(extractTree(_)(using DefContext(), ClassDefs())))
    }
  }

  def outOfSubsetError(pos: SourcePosition, msg: String): Nothing =
    throw frontend.UnsupportedCodeException(dottyPosToInoxPos(pos), msg)

  def outOfSubsetError(t: tpd.Tree, msg: String): Nothing = outOfSubsetError(t.sourcePos, msg)

  private case class DefContext(
    tparams: ListMap[Symbol, xt.TypeParameter] = ListMap(),
    vars: Map[Symbol, () => xt.Expr] = Map(),
    mutableVars: Map[Symbol, () => xt.Variable] = Map(),
    localFuns: Map[Symbol, (Identifier, Seq[xt.TypeParameterDef], xt.FunctionType)] = Map(),
    localClasses: Map[Identifier, xt.LocalClassDef] = Map(),
    depParams: Map[TermName, xt.ValDef] = Map(),
    typeParamRefs: Map[TypeParamRef, xt.TypeParameter] = Map(), // TODO: Say what is this thing
    isExtern: Boolean = false,
    resolveTypes: Boolean = false,
    wrappingArithmetic: Boolean = false,
  ) {
    def union(that: DefContext) = {
      copy(
        this.tparams ++ that.tparams,
        this.vars ++ that.vars,
        this.mutableVars ++ that.mutableVars,
        this.localFuns ++ that.localFuns,
        this.localClasses ++ that.localClasses,
        this.depParams ++ that.depParams,
        this.typeParamRefs ++ that.typeParamRefs,
        this.isExtern || that.isExtern,
        this.resolveTypes || that.resolveTypes,
        this.wrappingArithmetic || that.wrappingArithmetic,
      )
    }

    def isVariable(s: Symbol) = (vars contains s) || (mutableVars contains s)

    def withNewTypeParams(ntparams: Traversable[(Symbol, xt.TypeParameter)]) = {
      copy(tparams = tparams ++ ntparams)
    }

    def withNewTypeParam(tparam: (Symbol, xt.TypeParameter)) = {
      copy(tparams = tparams + tparam)
    }

    def withNewVars(nvars: Traversable[(Symbol, () => xt.Expr)]) = {
      copy(vars = vars ++ nvars)
    }

    def withNewVar(nvar: (Symbol, () => xt.Expr)) = {
      copy(vars = vars + nvar)
    }

    def withNewMutableVar(nvar: (Symbol, () => xt.Variable)) = {
      copy(mutableVars = mutableVars + nvar)
    }

    def withNewMutableVars(nvars: Traversable[(Symbol, () => xt.Variable)]) = {
      copy(mutableVars = mutableVars ++ nvars)
    }

    def withLocalFun(sym: Symbol, id: Identifier, tparams: Seq[xt.TypeParameterDef], tpe: xt.FunctionType) = {
      copy(localFuns = this.localFuns + (sym -> ((id, tparams, tpe))))
    }

    def withLocalClass(lcd: xt.LocalClassDef) = {
      copy(localClasses = this.localClasses + (lcd.id -> lcd))
    }

    def withDepParams(dps: Traversable[(TermName, xt.ValDef)]) = {
      copy(depParams = depParams ++ dps)
    }

    def setResolveTypes(resolveTypes: Boolean) = {
      copy(resolveTypes = resolveTypes)
    }

    def setWrappingArithmetic(wrappingArithmetic: Boolean) = {
      copy(wrappingArithmetic = wrappingArithmetic)
    }

    def withExtern(extern: Boolean) = {
      copy(isExtern = isExtern || extern)
    }
  }

  // This one never fails, on error, it returns Untyped
  private def stainlessType(tpt: Type)(using DefContext, SourcePosition, ClassDefs): xt.Type = {
    try {
      extractType(tpt)
    } catch {
      case e: frontend.UnsupportedCodeException =>
        reporter.debug(e.pos, "[ignored] " + e.getMessage, e)
        xt.Untyped
    }
  }

  private def extractImports(i: tpd.Import): Seq[xt.Import] = {
    def selectorChain(t: tpd.Tree): Seq[String] = t match {
      case Select(t2, name) => selectorChain(t2) :+ name.toString
      case Ident(name) => Seq(name.toString)
      case tpd.EmptyTree => Seq.empty
      case _ => outOfSubsetError(t, "Unexpected import selector: " + t)
    }

    val prefix = selectorChain(i.expr)
    // TODO: what about renames?
    val imports = i.selectors.map { impSel => prefix :+ impSel.imported.name.toString }

    imports.map {
      case path :+ "_" => xt.Import(path, true)
      case p => xt.Import(p, false)
    }
  }

  def extractRef(t: tpd.RefTree): Identifier = {
    def rec(t: tpd.Tree): Seq[String] = t match {
      case Select(t2, name) => rec(t2) :+ name.toString
      case Ident(name) => Seq(name.toString)
      case tpd.EmptyTree => Seq.empty
      case _ => outOfSubsetError(t, "Unexpected selector " + t)
    }

    val refs = (rec(t.qualifier) :+ t.name.toString).filter(_ != "<empty>")
    FreshIdentifier(refs.mkString("$"))
  }

  def extract(stats: List[tpd.Tree]): (
    Seq[xt.Import],
    Seq[Identifier],
    Seq[Identifier],
    Seq[Identifier],
    Seq[xt.ModuleDef],
    Seq[xt.ClassDef],
    Seq[xt.FunDef],
    Seq[xt.TypeDef],
    Option[Identifier]
  ) = extractStatic(stats)(using ClassDefs())

  private def extractStatic(stats: List[tpd.Tree])(using cds: ClassDefs): (
    Seq[xt.Import],
    Seq[Identifier],
    Seq[Identifier],
    Seq[Identifier],
    Seq[xt.ModuleDef],
    Seq[xt.ClassDef],
    Seq[xt.FunDef],
    Seq[xt.TypeDef],
    Option[Identifier]
  ) = {
    given DefContext = DefContext()
    val allClassDefs = cds.defs ++ stats.collect {
      case cd@ExClassDef() => cd
    }
    // Classes may also have corresponding ValDefs or DefDef for which the annotations are not propagated
    // For instance, if we consider:
    //
    //  @ignore
    //  implicit class WhileDecorations(val u: Unit) { /* ... */ }
    //
    // Then Dotty translates the original AST into:
    //
    //  @ignore
    //  class WhileDecorations(val u: Unit) { /* ... */ }
    //  // Note: the @ignore is not propagated
    //  def WhileDecorations(u: Unit): WhileDecorations = new WhileDecorations(u)
    //
    // So we need to add these annotations by ourselves.

    // TODO: What about syntectic stuff from ignored objects?
//    val ignoredClasses = allClassDefs.filter(td => annotationsOf(td.symbol).contains(xt.Ignore))
//      .map(_.symbol.name.toTermName)
//      .toSet
    val extraFlags = allClassDefs.map(td => td.symbol.name.toTermName -> annotationsOf(td.symbol)).toMap.withDefaultValue(Seq.empty)
    val ignoredClasses = extraFlags.filter(_._2.contains(xt.Ignore)).map(_._1).toSet
    given ClassDefs = ClassDefs(allClassDefs)

    var imports   : Seq[xt.Import]    = Seq.empty
    var classes   : Seq[Identifier]   = Seq.empty
    var functions : Seq[Identifier]   = Seq.empty
    var typeDefs  : Seq[Identifier]   = Seq.empty
    var subs      : Seq[xt.ModuleDef] = Seq.empty

    var allClasses   : Seq[xt.ClassDef] = Seq.empty
    var allFunctions : Seq[xt.FunDef]   = Seq.empty
    var allTypeDefs  : Seq[xt.TypeDef]  = Seq.empty

    var companionOf : Option[Identifier] = None

    for (d <- stats) d match {
      case tpd.EmptyTree =>
        // ignore
      // TODO: Fix this, as it makes top-level definition ignored!!!!
      case t if (
        annotationsOf(t.symbol).contains(xt.Ignore) /*||
        (t.symbol.is(Synthetic) && !canExtractSynthetic(t.symbol))*/
      ) =>
        // ignore

      // TODO: This is the object instantiation value. What should we do with it?
      case vd @ ValDef(_, _, _) if vd.symbol is Module =>
        // ignore

      case DefDef(nme, _, _, _) if ignoredClasses.contains(nme) =>
        // println("IGNORED: "+d)
        // ignore

      case t @ ExSymbol("stainless", "annotation", "ignore") if t.isInstanceOf[tpd.TypeDef] =>
        // don't extract the `ignore` annotation class

      case i @ Import(_, _) =>
        imports ++= extractImports(i)

      // TODO: missing bits
      case pd @ PackageDef(ref, stats) =>
        val (imports, classes, functions, typeDefs, modules, newClasses, newFunctions, newTypeDefs, _) = extractStatic(stats)
        subs :+= xt.ModuleDef(extractRef(ref), imports, classes, functions, typeDefs, modules)
        allClasses ++= newClasses
        allFunctions ++= newFunctions
        allTypeDefs ++= newTypeDefs

      case td @ ExObjectDef() =>
        val (obj, newClasses, newFunctions0, newTypeDefs) = extractObject(td)
        subs :+= obj
        allClasses ++= newClasses

        // Handling of default arguments
        // It turns out that `stats` is ordered s.t. a class is ordered before its companion module.
        // This is a desired ordering for the extraction of default arguments of classes.
        // If we have a case class such as:
        //
        //    case class Hello(x: Int = 123)
        //
        // Then Dotty transforms this source program into something like:
        //
        //   case class Hello(x: Int) { /* ... */ }
        //   class Hello$ {  // synthetized companion module
        //      def <init>$default$1: Int = 123
        //      // ...
        //   }
        //
        // The extraction process will take care of extracting <init>$default$1 but we would like to annotate that function
        // to be a default argument for Hello. To this end, we must first have extracted Hello before appropriately
        // annotating that function with @paramInit(Hello)
        val newFunctions = newFunctions0.flatMap { fd =>
          if (
            fd.id.name.startsWith("<init>$default$") &&
              !fd.flags.exists(_.isInstanceOf[xt.ClassParamInit])
          ) {
            val correspondingClassName = td.name.toTermName.underlying.toString
            val cdIdOpt = allClasses.flatMap(cd =>
              if (cd.id.name == correspondingClassName) Some(cd.id)
              else None)
            // We may not find the corresponding class. This can happen for @ignored classes having default argument
            // (their <init>$default functions however have not an explicit @ignore annotation, so we should remove them manually)
            cdIdOpt.map(cdId => fd.copy(flags = (xt.ClassParamInit(cdId) +: fd.flags)).setPos(fd))
          } else {
            Some(fd)
          }
        }
        allFunctions ++= newFunctions
        allTypeDefs ++= newTypeDefs

      /*
      // TODO: What is this supposed to do??? does not seem to work.
      case t @ DefDef(name, _, tpt, _)
        if (t.symbol is Synthetic) &&
          !canExtractSynthetic(t.symbol) &&
          name.toString == "apply" =>
        extractType(tpt) match {
          case xt.ClassType(cid, _) =>
            assert(companionOf.forall(_ != cid),
              s"Error during Stainless extraction, couldn't tie companion object to class: $cid"
            )
            companionOf = Some(cid)
          case _ =>
        }
      */
      // Also subsumes case md: ModuleDef equivalent in scalac
      // TODO: Or does it??? What is even a ModuleDef??
      case cd @ ExClassDef() =>
        val (xcd, newFunctions, newTypeDefs) = extractClass(cd)
        classes :+= xcd.id
        allClasses :+= xcd
        allFunctions ++= newFunctions
        allTypeDefs ++= newTypeDefs

      // TODO: Moved to get things like SetOps$ coming from implict class stuff
      // this case goes after `ExObjectDef` in order to explore synthetic objects that may contain
      // field initializers
      case t if (t.symbol is Synthetic) && !canExtractSynthetic(t.symbol) =>
      // ignore

      // TODO: Can be removed
      case ExFunctionDef(fsym, _, _, _, _) if fsym.name is NameKinds.ExtMethName =>
        // ignore

      // Normal function
      case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        val fd0 = extractFunction(fsym, dd, tparams, vparams, rhs)
        val fd = fd0.copy(flags = fd0.flags ++ extraFlags(fsym.name.toTermName))
        functions :+= fd.id
        allFunctions :+= fd

      case t @ ExMutableFieldDef(fsym, _, _) if annotationsOf(fsym).contains(xt.Extern) =>
        // Ignore @extern variables in static context

      // Normal fields
      case t @ ExFieldDef(fsym, _, rhs) =>
        val fd0 = extractFunction(fsym, t, Seq(), Seq(), rhs)
        val fd = fd0.copy(flags = fd0.flags ++ extraFlags(fsym.name.toTermName))
        functions :+= fd.id
        allFunctions :+= fd

      case t @ ExLazyFieldDef(fsym, _, rhs) =>
        val fd0 = extractFunction(fsym, t, Seq.empty, Seq.empty, rhs)
        val fd = fd0.copy(flags = fd0.flags ++ extraFlags(fsym.name.toTermName))
        functions :+= fd.id
        allFunctions :+= fd

//      case t @ ExFieldAccessorFunction(fsym, _, vparams, rhs) =>
//        val fd = extractFunction(fsym, t, Seq.empty, vparams, rhs)
//        functions :+= fd.id
//        allFunctions :+= fd
//
//      case t @ ExLazyFieldAccessorFunction(fsym, _, rhs) =>
//        val fd = extractFunction(fsym, t, Seq.empty, Seq.empty, rhs)
//        functions :+= fd.id
//        allFunctions :+= fd

      case t if t.symbol is Synthetic =>
        // ignore

      case t @ ExTypeDef() =>
        val td = extractTypeDef(t)
        typeDefs :+= td.id
        allTypeDefs :+= td

      case t @ ExMutableFieldDef(_, _, _) =>
        outOfSubsetError(t, "Mutable fields in static containers such as objects are not supported")

      case other =>
        reporter.warning(other.sourcePos, s"Stainless does not support the following tree in static containers:\n$other")
    }

    (imports, classes, functions, typeDefs, subs, allClasses, allFunctions, allTypeDefs, companionOf)
  }

  // TODO: comment
  private def extractHKTypeParams(params: List[LambdaParam])(using dctx0: DefContext, cds: ClassDefs): (DefContext, Seq[xt.TypeParameter]) =
    params.foldLeft((dctx0, Seq.empty[xt.TypeParameter])) {
      case ((dctx, tparams), param) =>
        val id = FreshIdentifier(param.paramName.toString)
        val paramRef = param.paramRef.asInstanceOf[TypeParamRef]
        // TODO: Test this variance thing. It seems to be incorrectly used
        val variance =
          if (param.paramVariance.is(Covariant)) Some(xt.Variance(true))
          else if (param.paramVariance.is(Contravariant)) Some(xt.Variance(true))
          else None
        val bounds = param.paramInfo match {
          case paramTb: TypeBounds if !paramTb.lo.isBottomType && !paramTb.hi.isTopType =>
            val dctxRec = dctx.copy(typeParamRefs = dctx.typeParamRefs + (paramRef -> xt.TypeParameter(id, variance.toSeq)))
            val (_, paramLo, paramHi) = extractTypeParams(paramTb)(using dctxRec)
            Some(xt.Bounds(paramLo, paramHi))
          case _ => None
        }
        val tp = xt.TypeParameter(id, variance.toSeq ++ bounds)
        (dctx.copy(typeParamRefs = dctx.typeParamRefs + (paramRef -> tp)), tparams :+ tp)
    }

  // TODO: comment
  private def extractTypeParams(bounds: TypeBounds)(using dctx0: DefContext, cds: ClassDefs): (Seq[xt.TypeParameter], xt.Type, xt.Type) = {
    given SourcePosition = NoSourcePosition
    val (dctx, tyParams, lo, hi) = bounds match {
      case TypeBounds(lo: HKTypeLambda, hi: HKTypeLambda) =>
        // TODO: assert that lo.typeParams and hi.typeParams are equivalent modulo their respective binder
        // We arbitrarily pick the upper bound as the "reference" for the type parameters
        val (dctx, tyParams) = extractHKTypeParams(hi.typeParams)
        // Substitute the body of the HK lambda to refer to the hi HK type parameters
        val loSubsted = lo.resType.subst(lo, hi)
        (dctx, tyParams, loSubsted, hi.resType)
      case TypeBounds(lo, hi: HKTypeLambda) =>
        val (dctx, tyParams) = extractHKTypeParams(hi.typeParams)
        (dctx, tyParams, lo, hi.resType)
      case TypeBounds(lo: HKTypeLambda, hi) =>
        val (dctx, tyParams) = extractHKTypeParams(lo.typeParams)
        (dctx, tyParams, lo.resType, hi)
      case TypeBounds(lo, hi) =>
        (dctx0, Seq.empty, lo, hi)
    }
    (tyParams, extractType(lo)(using dctx), extractType(hi)(using dctx))
  }

  // TODO: Review
  private def extractTypeDef(td: tpd.TypeDef)(using dctx: DefContext, cds: ClassDefs): xt.TypeDef = {
    given SourcePosition = NoSourcePosition
    val sym = td.symbol
    val id = getIdentifier(sym)
    val flags = annotationsOf(sym)
    // TODO: Test with type F[X] = ... and type F[X];
    val (tparams, body, isAbstract) = td.rhs match {
      // TODO: Are these following two cases ever possible? It seems we get a TypeTree of something, not TypeBoundsTree et al.
      case LambdaTypeTree(tparams, body) =>
        val typeParamsSymbols = typeParamSymbols(tparams)
        val typeParams = extractTypeParams(typeParamsSymbols)
        val tpCtx = dctx.withNewTypeParams(typeParamsSymbols zip typeParams)
        val typeBody = extractType(body)(using tpCtx)
        (typeParams, typeBody, false)

      case TypeBoundsTree(lo, hi, _) =>
        val (loType, hiType) = (extractType(lo), extractType(hi))
        (Seq.empty, xt.TypeBounds(loType, hiType, Seq.empty), true)

      case tt: tpd.TypeTree => tt.tpe match {
        case tb: TypeBounds =>
          val (tyParams, loType, hiType) = extractTypeParams(tb)
          (tyParams, xt.TypeBounds(loType, hiType, Seq.empty), true)
        // type F[X] = ...
        case hk: HKTypeLambda =>
          val (dctx, tyParams) = extractHKTypeParams(hk.typeParams)
          (tyParams, extractType(hk.resType)(using dctx), false)
        case t =>
          (Seq.empty, extractType(t), false)
      }

      case tpt =>
        val tpe =
          if (tpt.symbol is Opaque)
            tpt.symbol.typeRef.translucentSuperType
          else
            tpt.tpe

        (Seq.empty, extractType(tpt, tpe), false)
    }

    // Opaque types are referenced from their opaque right-hand side for some reason.
    val realId = if (td.rhs.symbol is Opaque) getIdentifier(td.rhs.symbol) else id

    new xt.TypeDef(
      realId,
      tparams.map(xt.TypeParameterDef(_)),
      body,
      flags ++ (if (isAbstract) Seq(xt.IsAbstract) else Seq.empty)
    )
  }

  private def extractObject(td: tpd.TypeDef)(using ClassDefs): (xt.ModuleDef, Seq[xt.ClassDef], Seq[xt.FunDef], Seq[xt.TypeDef]) = {
    val template = td.rhs.asInstanceOf[tpd.Template]
    /*
    // Filter out @invariant-annotated methods generated in companion module of case classes extending AnyVal.
    // For instance, following snippet:
    //  case class TestVal(x: Int) extends AnyVal {
    //    @invariant
    //    def inv = <inv-body>
    //  }
    // is (roughly) transformed by Dotty to:
    //  class TestVal(x: Int) extends AnyVal {
    //    @invariant
    //    def inv = TestVal.inv$extension(this)
    //  }
    //  val TestVal = new TestVal$
    //  class TestVal$ {
    //    @invariant
    //    def inv$extension(this$: TestVal) = <inv-body>
    //  }
    // Calling methods within an invariant is generally unsound, so we have to inline the call to TestVal.inv$extension(this)
    // The method inv$extension can then be filtered out, as it is done below.
    val filteredBody = template.body.filter {
      case dd: tpd.DefDef =>
        !((dd.symbol.name is NameKinds.ExtMethName) && annotationsOf(dd.symbol).contains(xt.IsInvariant))
      case _ => true
    }
    */
    val (imports, classes, functions, typeDefs, subs, allClasses, allFunctions, allTypeDefs, _) = extractStatic(template.body)

    val module = xt.ModuleDef(
      getIdentifier(td.symbol),
      imports,
      classes,
      functions,
      typeDefs,
      subs
    ).setPos(td.sourcePos)

    (module, allClasses, allFunctions, allTypeDefs)
  }

  private def isValidParentType(parent: Type, inLibrary: Boolean = false): Boolean =
    !isIgnored(parent) && !((parent frozen_=:= defn.ThrowableType) && inLibrary)

  private def isValidParent(parent: tpd.Tree, inLibrary: Boolean = false): Boolean =
    isValidParentType(parent.tpe, inLibrary)

  private def extractClass(td: tpd.TypeDef)(using dctx: DefContext, cds: ClassDefs): (xt.ClassDef, Seq[xt.FunDef], Seq[xt.TypeDef]) = {
    val sym = td.symbol.asClass
    val id = getIdentifier(sym)
    val template = td.rhs.asInstanceOf[tpd.Template]

    val isValueClass = template.parents.exists(_.tpe.typeSymbol == defn.AnyValClass)

    val annots = annotationsOf(sym)
    val flags = annots ++
      (if (isValueClass) Some(xt.ValueClass) else None) ++
      (if (sym isOneOf AbstractOrTrait) Some(xt.IsAbstract) else None) ++
      (if (sym is Sealed) Some(xt.IsSealed) else None) ++
      (if ((sym is ModuleClass) && (sym is Case)) Some(xt.IsCaseObject) else None)

    val tparams = extractTypeParams(sym.asClass.typeParams)(using DefContext())

    val tpCtx = dctx.copy(tparams = dctx.tparams ++ (sym.asClass.typeParams zip tparams))

    val classType = xt.ClassType(id, tparams)

    val inLibrary = flags exists (_.name == "library")
    val parents = template.parents
      .filter(isValidParent(_, inLibrary))
      .map(p => extractType(p.tpe)(using tpCtx.setResolveTypes(true), p.sourcePos)) // TODO: setResolveTypes not in Scalac
      .collect {
        case ct: xt.ClassType => ct
        case lct: xt.LocalClassType => lct.toClassType
      }

    def isField(vd: tpd.ValDef) = {
      !vd.symbol.is(Accessor) && vd.symbol.is(ParamAccessor)
    }
/*
    val vdTpts = template.constr.termParamss.flatten.map(_.tpt).toVector

    val vds = template.body
      .collect {
        case vd: tpd.ValDef if isField(vd) => vd
      }
      .zipWithIndex
      .map { case (vd, i) => (vd, vdTpts(i)) }
*/
    val vds = template.body.collect {
      // TODO: Changed
      // TODO: Why do we need this??? ^^^ use the commented code above maybe?
//      case vd: tpd.ValDef if !(vd.symbol is Implicit) && !(vd.symbol is Accessor) && (vd.symbol is CaseAccessor) && (vd.symbol is ParamAccessor) => vd
      case vd: tpd.ValDef if !(vd.symbol is Implicit) && !(vd.symbol is Accessor) && ((vd.symbol is CaseAccessor) || (vd.symbol is ParamAccessor)) => vd
      case vd: tpd.ValDef if (vd.symbol is Implicit) && !(vd.symbol is Accessor) && (vd.symbol is ParamAccessor) => vd
    }

    val fields = vds map { case vd =>
      val vdSym = vd.symbol
      val id = getIdentifier(vdSym)
      val flags = annotationsOf(vdSym, ignoreOwner = true)
      val tpe = stainlessType(vd.tpt.tpe)(using tpCtx, vd.tpt.sourcePos)
      val (isExtern, isPure) = (flags contains xt.Extern, flags contains xt.IsPure)
      val isMutable = (vdSym is Mutable) || isExtern && !isPure

      (if (isMutable) xt.VarDef(id, tpe, flags) else xt.ValDef(id, tpe, flags)).setPos(vd.sourcePos)
    }

    val fieldsMap = vds.zip(fields).map {
      case (vd, field) => (vd.symbol, field.tpe)
    }.toMap

    val hasExternFields = fields.exists(_.flags.contains(xt.Extern))

    // TODO: different from scalac because dotty may generate something like Ident(myField) instead of the more precise Select(This(Ident(<class>)), myField)
    val defCtx = tpCtx // tpCtx.withNewVars(vds.map(_.symbol) zip fields.map(vd => () => vd.toVariable))

    var invariants: Seq[xt.Expr] = Seq.empty
    var methods: Seq[xt.FunDef] = Seq.empty
    var typeMembers: Seq[xt.TypeDef] = Seq.empty

    // We collect the methods and fields
    for ((d, i) <- template.body.zipWithIndex) d match {
      case tpd.EmptyTree =>
        // ignore

      case i: tpd.Import =>
        // ignore

      case t if t.symbol.is(Synthetic) && !canExtractSynthetic(t.symbol) =>
        // ignore

      case t if annotationsOf(t.symbol).contains(xt.Ignore) && !(t.symbol is CaseAccessor) =>
        // ignore

      case t if (t.symbol is Synthetic) && !canExtractSynthetic(t.symbol) =>
        // ignore

      case dd @ DefDef(nme.CONSTRUCTOR, _, _, _) =>
        // ignore

      // TODO
//      case ExCaseClassSyntheticJunk() | ExConstructorDef() =>
//       ignore

      // TODO: ?
      case td @ TypeDef(_, _) if td.symbol is Param =>
        // ignore

      // TODO: Not in Scalac
//      case cd @ ExClassDef() =>
//        outOfSubsetError(cd.sourcePos, "Classes can only be defined at the top-level, within objects, or within methods")

      // Class invariants
      case ExRequiredExpression(body, isStatic) =>
        def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
        invariants :+= wrap(extractTree(body)(using defCtx))

      // We cannot extract copy method if the class has extern fields as
      // the type of copy and the getters mention what might be a type we
      // cannot extract.
      case t @ ExFunctionDef(fsym, _, _, _, _)
        if hasExternFields && (isCopyMethod(fsym) || isDefaultGetter(fsym)) =>
          () // ignore

      case ExFunctionDef(fsym, _, _, _, _) if fsym.name is NameKinds.ExtMethName =>
        // ignore

      // Normal methods
      case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        methods :+= extractFunction(fsym, dd, tparams, vparams, rhs)(using defCtx)

      // FIXME: contrarily to scalac, dotty does not generate accessor fns for field.
      //  With Scala 2, given a field (whether ctor or non-ctor), we get a pair of definitions: the val itself and its accessor fn.
      //  For *non-ctor fields*, the Scalac frontend creates a pair of *functions* as well:
      //  one for the val (annotated as @field) and one for the accessor (annotated as @accessor).
      //  However, with Dotty, we do not get an accessor fn.
      //  Since we must create one function for the field using the val symbol, we can't create
      //  an accessor fn with the same val symbol, as it's already been used.
      //  As such, it seems we cannot create an accessor fn... Or do we? there is this commented getIdentifier thing in ExThisCall
      case t @ ExFieldDef(fsym, _, rhs) =>
        val fd = extractFunction(fsym, t, Seq.empty, Seq.empty, rhs)(using defCtx)
        // FIXME: A field should not be annotated as an accessor of itself!!!!
        methods :+= fd.copy(flags = fd.flags ++ Seq(xt.FieldDefPosition(i), xt.IsAccessor(Some(getIdentifier(fsym)))))

      case t @ ExLazyFieldDef(fsym, _, rhs) =>
        methods :+= extractFunction(fsym, t, Seq.empty, Seq.empty, rhs)(using defCtx)

      case t @ ExMutableFieldDef(_, _, rhs) if rhs != tpd.EmptyTree =>
        outOfSubsetError(t, "Mutable fields in traits or abstract classes cannot have default values")

      case vd @ ExMutableFieldDef(sym, _, _) if vd.symbol.owner isOneOf AbstractOrTrait =>
        // TODO: Are we guarenteed to have vd.rhs = EmptyTree?
        methods :+= extractFunction(sym, vd, Seq.empty, Seq.empty, tpd.EmptyTree)(using defCtx)

      // FIXME: this is setter thing
      case t @ ExFieldAccessorFunction(sym, _, vparam, rhs) =>
        methods :+= extractFunction(sym, t, Seq.empty, List(vparam), rhs)(using defCtx)

      case td @ TypeDef(_, _) if !td.isClassDef =>
        typeMembers :+= extractTypeDef(td)(using defCtx)

      // TODO: Verify how things behave for var
      // Corresponds to constructor fields.
      // We generate an accessor function for them (with the RHS just being a select over that field)
      case vd@ValDef(_, _, _) =>
        val fd = extractFunction(vd.symbol, vd, Seq.empty, Seq.empty, tpd.Ident(vd.tpe.asInstanceOf[TermRef]))(using defCtx)
        // We furthermore artificially add an IsAccessor flag to inform that this function is an accessor fn.
        // TODO: Check this
        methods :+= fd // .copy(flags = fd.flags :+ xt.IsAccessor(Some(getIdentifier(vd.symbol))))

      case d if d.symbol is Synthetic =>
        // ignore

      case d if d.symbol is Mutable =>
        // ignore

      case other =>
        reporter.warning(other.sourcePos, s"In class $id, Stainless does not support:\n$other")
    }

    val optInv = if (invariants.isEmpty) None else Some({
      val id = cache fetchInvIdForClass sym
      val pos = inox.utils.Position.between(invariants.map(_.getPos).min, invariants.map(_.getPos).max)
      new xt.FunDef(id, Seq.empty, Seq.empty, xt.BooleanType().setPos(pos),
        if (invariants.size == 1) invariants.head else xt.And(invariants).setPos(pos),
        (Seq(xt.IsInvariant) ++
          annots.filterNot(annot =>
            annot == xt.IsMutable ||
              annot.name == "cCode.export" ||
              annot.name.startsWith("cCode.global")
          )
        ).distinct
      ).setPos(pos)
    })

    val allMethods = (methods ++ optInv).map(fd => fd.copy(flags = fd.flags :+ xt.IsMethodOf(id)))
    val allTypeMembers = typeMembers.map(td => td.copy(flags = td.flags :+ xt.IsTypeMemberOf(id)))

    val xcd = new xt.ClassDef(
      id,
      tparams.map(xt.TypeParameterDef(_)),
      parents,
      fields,
      flags
    ).setPos(sym.sourcePos)

    (xcd, allMethods, allTypeMembers)
  }

  private def extractFunction(
    sym: Symbol,
    tree: tpd.ValOrDefDef,
    tparams: Seq[tpd.TypeDef],
    vparams: Seq[tpd.ValDef],
    rhs: tpd.Tree,
    typeParams: Option[Seq[xt.TypeParameter]] = None
  )(using dctx: DefContext, cds: ClassDefs): xt.FunDef = {
    def isByName(param: tpd.ValDef) = param.tpt match {
      case ByNameTypeTree(_) => true
      case tt@TypeTree() => tt.tpe match {
        case _: ExprType => true
        case _ => false
      }
      case _ => false
    }
    // TODO: Explain (due to dotty not preserving annotation of original methods)
    val extraFlags = sym.name.match {
      case DerivedName(baseFnName, info) if info.kind == NameKinds.ExtMethName =>
        cds.defs.flatMap(_.rhs match {
          case tpl@Template(_, _, _, _) =>
            val res = tpl.body.collectFirst {
              case dd@DefDef(candidateName, _, _, _) if candidateName == baseFnName =>
                dd.termParamss.flatten.map(vd => vd.symbol.name -> annotationsOf(vd.symbol, ignoreOwner = true)).toMap
            }
            res
          case _ => None // should not arise
        }).headOption.getOrElse(Map.empty[Name, Seq[xt.Flag]])
      case _ =>
        Map.empty[Name, Seq[xt.Flag]]
    }.withDefaultValue(Seq.empty[xt.Flag])

    // Type params of the function itself
    val extparams = typeParamSymbols(tparams)
    val ntparams = typeParams.getOrElse(extractTypeParams(extparams))

    val tctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip ntparams).toMap/*, resolveTypes = true*/) // TODO: No resolvetypes in Scalac

    // TODO: There are some differences with Scalac (vdefs instead of sym.info.paramss)
    val (newParams, nctx) = vparams.foldLeft((Seq.empty[xt.ValDef], tctx)) {
      case ((vds, vctx), param) =>
        val paramSym: Symbol = param.symbol
        val byName = isByName(param) // TODO: Ensure correct transformation when e.g. passing byname to byname, byname to byval etc.
        val ptpe = stainlessType(param.tpt.tpe)(using vctx, paramSym.sourcePos)
        val tpe = if (byName) xt.FunctionType(Seq(), ptpe).setPos(paramSym.sourcePos) else ptpe
        val flags = annotationsOf(paramSym, ignoreOwner = true) ++ extraFlags(paramSym.name)
        val vd = xt.ValDef(getIdentifier(paramSym), tpe, flags).setPos(paramSym.sourcePos)
        val expr = if (byName) {
          () => xt.Application(vd.toVariable, Seq()).setPos(vd)
        } else {
          () => vd.toVariable
        }
        (vds :+ vd, vctx.withNewVar(param.symbol -> expr))
    }

    val id = getIdentifier(sym)
    val isAbstract = rhs == tpd.EmptyTree
    val isFld = sym.isField
    val isCtorField = sym.isField && ((sym is ParamAccessor) || (sym is CaseAccessor))
    val isNonCtorField = sym.isField && !(sym is ParamAccessor) && !(sym is CaseAccessor)
    // TODO: There are some differences with Scalac
    var flags = annotationsOf(sym).filterNot(annot => annot == xt.IsMutable || annot.name == "inlineInvariant") ++
      (if ((sym is Implicit) && (sym is Synthetic)) Seq(xt.Inline, xt.Synthetic) else Seq()) ++
      (if (sym is Inline) Seq(xt.Inline) else Seq()) ++
      (if (sym is Private) Seq(xt.Private) else Seq()) ++
      (if (sym is Final) Seq(xt.Final) else Seq()) ++
      (if (!isAbstract && (isNonCtorField || (sym is Lazy))) Seq(xt.IsField(sym is Lazy)) else Seq()) ++
      // TODO: check this one
      (if (isDefaultGetter(sym) || isCopyMethod(sym)) Seq(xt.Synthetic, xt.Inline) else Seq()) ++
//      (if ((/*isAbstract && */sym.isField) || (!(sym is Lazy) && (sym is Accessor)) || isCtorField) // TODO: isAbstract commenté, car on aimerait avoir val x = 123 (se trouvant ds un trait) marqué comme accessor
//        Seq(xt.IsAccessor(Option(getIdentifier(sym.underlyingSymbol)).filterNot(_ => isAbstract)))
      // TODO: check this one
      // TODO: This version makes FreshCopy fail, because val o does not get annotated @accessor (it needs @field and @accessor?????)
      (if ((isAbstract && sym.isField) || (!(sym is Lazy) && (sym is Accessor)) || isCtorField)
        Seq(xt.IsAccessor(Option(getIdentifier(sym.underlyingSymbol)).filterNot(_ => isAbstract)))
      /*
      // TODO: What should we do with this xt.IsField ?
      //  What about non-param fields? should we @field them or not?
      //  What about lazy fields?
      (if (!isAbstract && ((sym.isField) || (sym is Lazy))) Seq(xt.IsField(sym is Lazy)) else Seq()) ++
      (if (isDefaultGetter(sym) || isCopyMethod(sym)) Seq(xt.Synthetic, xt.Inline) else Seq()) ++
      (if ((isAbstract && sym.isField) || (!(sym is Lazy) && (sym is Accessor)))
        Seq(xt.IsAccessor(Option(getIdentifier(sym.underlyingSymbol)).filterNot(_ => isAbstract)))
      */
      else Seq())

//    if (sym.isField && !isAbstract && !((!(sym is Lazy) && (sym is Accessor)) || isCtorField)) {
//      println("plop")
//    }

    // @cCode.drop implies @extern
    if (flags.exists(_.name == "cCode.drop"))
      flags :+= xt.Extern

    // TODO: There are some differences with Scalac
    if (sym.name == nme.unapply) {
      val isEmptyDenot = typer.Applications.extractorMember(sym.info.finalResultType, nme.isEmpty)
      val getDenot = typer.Applications.extractorMember(sym.info.finalResultType, nme.get)
      flags :+= xt.IsUnapply(getIdentifier(isEmptyDenot.symbol), getIdentifier(getDenot.symbol))
    }

    // TODO: comment: we want to inline things like toListPost$extension
    val body = rhs /*
      /*if (!flags.contains(xt.IsInvariant)) rhs
      else */rhs match {
        case ExCall(_, extMethSym, _, _) if (extMethSym.name is NameKinds.ExtMethName) =>
          val clsSym = extMethSym.denot.owner.asClass
          val clsDef = cds.defs.find(_.symbol eq clsSym).get
          val template = clsDef.rhs.asInstanceOf[tpd.Template]
          val methDef = template.body.collectFirst {
            case d@DefDef(nme, _, _, _) if nme == extMethSym.name => d
          }.get
          val inl = new typer.Inliner(rhs, methDef.rhs)
          val res = inl.inlined(rhs)
          res.asInstanceOf[tpd.Inlined].expansion
        case _ =>
          // Not calling an extension method (which is the case for non-value classes)
          rhs
      }*/
    val paramsMap = (vparams zip newParams).map { case (param, vd) =>
      param.symbol -> (if (isByName(param)) () => xt.Application(vd.toVariable, Seq()).setPos(vd.toVariable) else () => vd.toVariable)
    }.toMap

    val fctx = nctx
      .withNewVars(paramsMap)
      .copy(tparams = dctx.tparams ++ (tparams.map(_.symbol) zip ntparams))
      .copy(isExtern = dctx.isExtern || (flags contains xt.Extern))

    lazy val retType = extractType(tree.tpt, sym.info.finalResultType)(using nctx) // TODO: Should be fctx?

    val (finalBody, returnType) = if (isAbstract) {
      flags :+= xt.IsAbstract
      (xt.NoTree(retType).setPos(sym.sourcePos), retType)
    } else {
      val fullBody = xt.exprOps.flattenBlocks(extractTreeOrNoTree(body)(using fctx))
      val localClasses = xt.exprOps.collect[xt.LocalClassDef] {
        case xt.LetClass(lcds, _) => lcds.toSet
        case _ => Set()
      } (fullBody)
      val xyz = 3
      if (localClasses.isEmpty) (fullBody, retType)
      else {
        // If the function contains local classes, we need to add those to the
        // context in order to type its body.
        val tctx = localClasses.toSeq.foldLeft(nctx)(_ withLocalClass _)

        val returnType = stainlessType(sym.info.finalResultType)(using tctx, sym.sourcePos)
        val bctx = fctx.copy(localClasses = fctx.localClasses ++ tctx.localClasses)
        // FIXME: `flattenBlocks` should not change the positions that appear in `ntparams`
        (xt.exprOps.flattenBlocks(extractTreeOrNoTree(body)(using bctx)), returnType)
      }
    }

    object KeywordChecker extends xt.ConcreteStainlessSelfTreeTraverser {
      override def traverse(e: xt.Expr) = {
        e match {
          case _: xt.Require =>
            reporter.warning(e.getPos, s"This require is ignored for verification because it is not at the top-level of this @extern function.")
          case _: xt.Ensuring =>
            reporter.warning(e.getPos, s"This ensuring is ignored for verification because it is not at the top-level of this @extern function.")
          case _: xt.Reads =>
            reporter.warning(e.getPos, s"This reads is ignored for verification because it is not at the top-level of this @extern function.")
          case _: xt.Modifies =>
            reporter.warning(e.getPos, s"This modifies is ignored for verification because it is not at the top-level of this @extern function.")
          case _ =>
            ()
        }
        super.traverse(e)
      }
    }

    // TODO: extension method call
    val fullBody = if (fctx.isExtern) {
      val specced = xt.exprOps.BodyWithSpecs(finalBody)
      specced.bodyOpt foreach { KeywordChecker.traverse }
      specced.withBody(xt.NoTree(returnType)).reconstructed.setPos(body.sourcePos)
    } else {
      finalBody
    }

    new xt.FunDef(
      id,
      ntparams.map(tp => xt.TypeParameterDef(tp)),
      newParams,
      returnType,
      fullBody,
      flags.distinct
    ).setPos(sym.sourcePos)
  }

  private def typeParamSymbols(tdefs: Seq[tpd.TypeDef]): Seq[Symbol] = tdefs.flatMap(_.tpe match {
    case tp @ TypeRef(_, _) =>
      Some(tp.symbol)
    case t =>
      outOfSubsetError(t.typeSymbol.sourcePos, "Unhandled type for parameter: "+t)
      None
  })

  private def extractTypeParams(syms: Seq[Symbol])(using dctx: DefContext, cds: ClassDefs): Seq[xt.TypeParameter] = {
    syms.foldLeft((dctx, Seq[xt.TypeParameter]())) { case ((dctx, tparams), sym) =>
      val variance =
        if (sym is Covariant) Some(xt.Variance(true))
        else if (sym is Contravariant) Some(xt.Variance(false))
        else None

      val bounds = sym.info match {
        case TypeBounds(lo, hi) =>
          val (loType, hiType) = (extractType(lo)(using dctx, sym.sourcePos), extractType(hi)(using dctx, sym.sourcePos))
          if (loType != xt.NothingType() || hiType != xt.AnyType()) Some(xt.Bounds(loType, hiType))
          else None
        case _ => None
      }

      val flags = annotationsOf(sym, ignoreOwner = true)
      val tp = xt.TypeParameter(getIdentifier(sym), flags ++ variance.toSeq ++ bounds).setPos(sym.sourcePos)
      (dctx.copy(tparams = dctx.tparams + (sym -> tp)), tparams :+ tp)
    }._2
  }

  private def extractPattern(p: tpd.Tree, binder: Option[xt.ValDef] = None)(using dctx: DefContext, cds: ClassDefs): (xt.Pattern, DefContext) = p match {
    case b @ Bind(name, t @ Typed(pat, tpt)) =>
      val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt), annotationsOf(b.symbol, ignoreOwner = true)).setPos(b.sourcePos)
      val pctx = dctx.withNewVar(b.symbol -> (() => vd.toVariable))
      extractPattern(t, Some(vd))(using pctx)

    case b @ Bind(name, pat) =>
      val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(b), annotationsOf(b.symbol, ignoreOwner = true)).setPos(b.sourcePos)
      val pctx = dctx.withNewVar(b.symbol -> (() => vd.toVariable))
      extractPattern(pat, Some(vd))(using pctx)

    case t @ Typed(Ident(nme.WILDCARD), tpt) =>
      extractType(tpt)(using dctx.setResolveTypes(true)) match {
        case ct: xt.ClassType =>
          (xt.InstanceOfPattern(binder, ct).setPos(p.sourcePos), dctx)

        case lt =>
          outOfSubsetError(tpt, "Invalid type "+tpt.tpe+" for .isInstanceOf")
      }

    case Ident(nme.WILDCARD) =>
      (xt.WildcardPattern(binder).setPos(p.sourcePos), dctx)

    // TODO: Difference with Scalac (isOneOf ... Module)
    case s @ Select(_, b) if s.tpe.widenDealias.typeSymbol isOneOf (Case | Module) =>
      extractType(s)(using dctx.setResolveTypes(true)) match {
        case ct: xt.ClassType =>
          (xt.ClassPattern(binder, ct, Seq()).setPos(p.sourcePos), dctx)
        case _ =>
          outOfSubsetError(s, "Invalid instance pattern: "+s)
      }

    case id @ Ident(_) if id.symbol isOneOf (Case | Module) =>
      extractType(id)(using dctx.setResolveTypes(true)) match {
        case ct: xt.ClassType =>
          (xt.ClassPattern(binder, ct, Seq()).setPos(p.sourcePos), dctx)
        case _ =>
          outOfSubsetError(id, "Invalid instance pattern: "+id)
      }

    case a @ Apply(fn, args) =>
      extractType(a)(using dctx.setResolveTypes(true)) match {
        case ct: xt.ClassType =>
          val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip
          val nctx = subDctx.foldLeft(dctx)(_ union _)
          (xt.ClassPattern(binder, ct, subPatterns).setPos(p.sourcePos), nctx)

        case xt.TupleType(argsTpes) =>
          val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip
          val nctx = subDctx.foldLeft(dctx)(_ union _)
          (xt.TuplePattern(binder, subPatterns).setPos(p.sourcePos), nctx)

        case _ =>
          outOfSubsetError(a, "Invalid type "+a.tpe+" for .isInstanceOf")
      }

    case ExBigIntPattern(l) =>
      val lit = xt.IntegerLiteral(BigInt(l.const.stringValue))
      (xt.LiteralPattern(binder, lit), dctx)

    case ExInt8Literal(i)    => (xt.LiteralPattern(binder, xt.Int8Literal(i)),    dctx)
    case ExInt16Literal(i)   => (xt.LiteralPattern(binder, xt.Int16Literal(i)),   dctx)
    case ExInt32Literal(i)   => (xt.LiteralPattern(binder, xt.Int32Literal(i)),   dctx)
    case ExInt64Literal(i)   => (xt.LiteralPattern(binder, xt.Int64Literal(i)),   dctx)
    case ExBooleanLiteral(b) => (xt.LiteralPattern(binder, xt.BooleanLiteral(b)), dctx)
    case ExUnitLiteral()     => (xt.LiteralPattern(binder, xt.UnitLiteral()),     dctx)
    case ExStringLiteral(s)  => (xt.LiteralPattern(binder, xt.StringLiteral(s)),  dctx)

    // TODO: The following two cases are different from Scalac
    case t @ Typed(UnApply(f, _, pats), tp) =>
      val (subPatterns, subDctx) = pats.map(extractPattern(_)).unzip
      val nctx = subDctx.foldLeft(dctx)(_ union _)

      val sym = f.symbol
      if (sym.owner.exists && sym.owner.is(Synthetic) &&
          sym.owner.companionClass.exists && sym.owner.companionClass.is(Case)) {
        val ct = extractType(tp).asInstanceOf[xt.ClassType]
        (xt.ClassPattern(binder, ct, subPatterns).setPos(p.sourcePos), nctx)
      } else {
        val id = getIdentifier(sym)
        val tps = f match { case TypeApply(un, tps) => tps map extractType case _ => Seq.empty }
        (xt.UnapplyPattern(binder, Seq(), id, tps, subPatterns).setPos(t.sourcePos), nctx)
      }

    case UnApply(f, _, pats) =>
      val (subPatterns, subDctx) = pats.map(extractPattern(_)).unzip
      val nctx = subDctx.foldLeft(dctx)(_ union _)

      val sym = f.symbol
      if (sym.owner.exists && TupleSymbol.unapply(sym.owner.companionClass).isDefined) {
        (xt.TuplePattern(binder, subPatterns), nctx)
      } else if (sym.owner.exists && sym.owner.is(Synthetic) &&
          sym.owner.companionClass.exists && sym.owner.companionClass.is(Case)) {
        val id = getIdentifier(sym.owner.companionClass)
        val tps = f match { case TypeApply(un, tps) => tps map extractType case _ => Seq.empty }
        (xt.ClassPattern(binder, xt.ClassType(id, tps).setPos(p.sourcePos), subPatterns).setPos(p.sourcePos), nctx)
      } else {
        val id = getIdentifier(sym)
        val tps = f match { case TypeApply(un, tps) => tps map extractType case _ => Seq.empty }
        (xt.UnapplyPattern(binder, Seq(), id, tps, subPatterns).setPos(p.sourcePos), nctx)
      }

    case _ =>
      outOfSubsetError(p, "Unsupported pattern: "+p)
  }

  private def extractMatchCase(cd: tpd.CaseDef)(using dctx: DefContext, cds: ClassDefs): xt.MatchCase = {
    val (recPattern, ndctx) = extractPattern(cd.pat)
    val recBody             = extractTree(cd.body)(using ndctx)

    if (cd.guard == tpd.EmptyTree) {
      xt.MatchCase(recPattern, None, recBody).setPos(cd.sourcePos)
    } else {
      val recGuard = extractTree(cd.guard)(using ndctx)
      xt.MatchCase(recPattern, Some(recGuard), recBody).setPos(cd.sourcePos)
    }
  }

  private def extractTreeOrNoTree(tr: tpd.Tree)(using dctx: DefContext, cds: ClassDefs): xt.Expr = {
    try {
      extractTree(tr)
    } catch {
      case e: frontend.UnsupportedCodeException =>
        if (dctx.isExtern) {
          // println(e)
          xt.NoTree(extractType(tr)).setPos(tr.sourcePos)
        } else {
          throw e
        }
    }
  }

  private def extractSeq(args: Seq[tpd.Tree])(using dctx: DefContext, cds: ClassDefs): Seq[xt.Expr] = args match {
    case Seq(SeqLiteral(es, _)) =>
      es.map(extractTree)
    case Seq(Typed(SeqLiteral(es, _), tpt)) if tpt.tpe.typeSymbol == defn.RepeatedParamClass =>
      es.map(extractTree)
    case _ =>
      args.map(extractTree)
  }

  // TODO: Review
  private def extractBlock(es: List[tpd.Tree])(using dctx: DefContext, cds: ClassDefs): xt.Expr = {
    val fctx = es.collect {
      case ExFunctionDef(sym, tparams, vparams, tpt, rhs) => (sym, tparams, vparams)
    }.foldLeft(dctx) { case (dctx, (sym, tparams, vparams)) =>
      val extparams = typeParamSymbols(tparams)
      val ntparams = extractTypeParams(extparams)(using dctx)
      val nctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip ntparams))

      val tparamDefs = ntparams.map(tp => xt.TypeParameterDef(tp).copiedFrom(tp))

      val tpe = xt.FunctionType(
        vparams.map { param =>
          val tpe = stainlessType(param.tpe)(using nctx, param.tpt.sourcePos)
          param.tpt match {
            case ByNameTypeTree(_) => xt.FunctionType(Seq(), tpe).setPos(param.tpt.sourcePos)
            case _ => tpe
          }
        },
        stainlessType(sym.info.finalResultType)(using nctx, sym.sourcePos)
      ).setPos(sym.sourcePos)

      dctx.withLocalFun(sym, getIdentifier(sym), tparamDefs, tpe)
    }

    val (vds, vctx) = es.collect {
      case v @ ValDef(name, tpt, _) => (v.symbol, name, tpt)
    }.foldLeft((Map.empty[Symbol, xt.ValDef], fctx)) { case ((vds, dctx), (sym, name, tpt)) =>
      if (sym is Mutable) {
        val vd = xt.VarDef(FreshIdentifier(name.toString), extractType(tpt)(using dctx), annotationsOf(sym, ignoreOwner = true)).setPos(sym.sourcePos)
        (vds + (sym -> vd), dctx.withNewMutableVar((sym, () => vd.toVariable)))
      } else {
        val laziness = if (sym is Lazy) Some(xt.Lazy) else None
        val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt)(using dctx), annotationsOf(sym, ignoreOwner = true) ++ laziness).setPos(sym.sourcePos)
        (vds + (sym -> vd), dctx.withNewVar((sym, () => vd.toVariable)))
      }
    }

    val (lcds, cctx) = es.collect {
      case cd @ ExClassDef() => cd
    }.foldLeft((Map.empty[Symbol, xt.LocalClassDef], vctx)) { case ((lcds, dctx), cd) =>
      val (xcd, methods, typeDefs) = extractClass(cd)(using dctx)
      val lcd = xt.LocalClassDef(xcd, methods, typeDefs)
      (lcds + (cd.symbol -> lcd), dctx.withLocalClass(lcd))
    }

    def rec(es: List[tpd.Tree]): xt.Expr = es match {
      case Nil => xt.UnitLiteral()

      case (i: tpd.Import) :: xs => rec(xs)

      case (e @ ExAssertExpression(contract, oerr, isStatic)) :: xs =>
        def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x

        val contr = extractTree(contract)(using cctx)
        val b = contr match {
          // If we encounter an assert(false) as the last statement, we can refine the return type to Nothing by
          // having the body of the xt.Assert to be a NoTree of Nothing.
          case xt.BooleanLiteral(false) if xs.isEmpty =>
            xt.NoTree(xt.NothingType())
          case _ => rec(xs)
        }
        xt.Assert(wrap(contr), oerr, b).setPos(e.sourcePos)

      case (e @ ExRequiredExpression(contract, isStatic)) :: xs =>
        def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x

        val pre = extractTree(contract)(using cctx)
        val b   = rec(xs)
        xt.Require(wrap(pre), b).setPos(e.sourcePos)

      case (e @ ExDecreases(ranks)) :: xs =>
        val measure = xt.tupleWrap(ranks.map(extractTree(_)(using cctx)))
        val b       = rec(xs)
        xt.Decreases(measure, b).setPos(e.sourcePos)

      case (e @ ExReadsExpression(objs)) :: xs =>
        xt.Reads(extractTree(objs)(using cctx), rec(xs)).setPos(e.sourcePos)

      case (e @ ExModifiesExpression(objs)) :: xs =>
        xt.Modifies(extractTree(objs)(using cctx), rec(xs)).setPos(e.sourcePos)

      case (d @ ExFunctionDef(sym, tparams, params, ret, b)) :: xs =>
        val (id, tdefs, _) = cctx.localFuns(sym)
        val fd = extractFunction(sym, d, tparams, params, b, typeParams = Some(tdefs.map(_.tp)))(using cctx)
        val letRec = xt.LocalFunDef(id, tdefs, fd.params, fd.returnType, fd.fullBody, fd.flags).setPos(d.sourcePos)

        rec(xs) match {
          case xt.LetRec(defs, body) => xt.LetRec(letRec +: defs, body).setPos(d.sourcePos)
          case other => xt.LetRec(Seq(letRec), other).setPos(d.sourcePos)
        }

      case (cd @ ExClassDef()) :: xs =>
        val lcd = lcds(cd.symbol)

        // Drop companion object and/or synthetic modules Dotty inserts after local class declarations
        val rest = xs.dropWhile(x => x.symbol.is(Synthetic) && x.symbol.is(Module))
        rec(rest) match {
          case xt.LetClass(defs, body) => xt.LetClass(lcd +: defs, body).setPos(cd.sourcePos)
          case other => xt.LetClass(Seq(lcd), other).setPos(cd.sourcePos)
        }

      case (v @ ValDef(name, tpt, _)) :: xs =>
        if (v.symbol is Mutable) {
          xt.LetVar(vds(v.symbol), extractTree(v.rhs)(using cctx), rec(xs)).setPos(v.sourcePos)
        } else {
          xt.Let(vds(v.symbol), extractTree(v.rhs)(using cctx), rec(xs)).setPos(v.sourcePos)
        }
      // TODO: review. Not bresent for Scalac
      /*
      case ExWhileWithInvariant(cond, body, pred) :: xs =>
        val wh = xt.While(extractTree(cond)(using cctx), extractTree(body)(using cctx), Some(extractTree(pred)(using cctx)), None, Seq.empty).setPos(es.head.sourcePos)
        rec(xs) match {
          case xt.Block(elems, last) => xt.Block(wh +: elems, last).setPos(es.head.sourcePos)
          case e => xt.Block(Seq(wh), e).setPos(es.head.sourcePos)
        }

      case ExWhile(cond, body) :: xs =>
        val wh = xt.While(extractTree(cond)(using cctx), extractTree(body)(using cctx), None, None, Seq.empty).setPos(es.head.sourcePos)
        rec(xs) match {
          case xt.Block(elems, last) => xt.Block(wh +: elems, last).setPos(es.head.sourcePos)
          case e => xt.Block(Seq(wh), e).setPos(es.head.sourcePos)
        }
      */
      case x :: Nil =>
        extractTree(x)(using cctx)

      case (x @ Block(_, _)) :: rest =>
        val re = rec(rest)
        val (elems, last) = re match {
          case xt.Block(elems, last) => (elems, last)
          case e => (Seq(), e)
        }

        extractTree(x)(using cctx) match {
          case xt.Decreases(m, b) => xt.Decreases(m, xt.Block(b +: elems, last).setPos(re)).setPos(x.sourcePos)
          case xt.Require(pre, b) => xt.Require(pre, xt.Block(b +: elems, last).setPos(re)).setPos(x.sourcePos)
          case xt.Reads(objs, b) => xt.Reads(objs, xt.Block(b +: elems, last).setPos(re)).setPos(x.sourcePos)
          case xt.Modifies(objs, b) => xt.Modifies(objs, xt.Block(b +: elems, last).setPos(re)).setPos(x.sourcePos)
          case b => xt.Block(b +: elems, last).setPos(x.sourcePos)
        }

      case x :: rest =>
        rec(rest) match {
          case xt.Block(elems, last) =>
            xt.Block(extractTree(x)(using cctx) +: elems, last).setPos(x.sourcePos)
          case e =>
            xt.Block(Seq(extractTree(x)(using cctx)), e).setPos(x.sourcePos)
        }
    }

    rec(es)
  }

  private def extractArgs(sym: Symbol, args: Seq[tpd.Tree])(using dctx: DefContext, cds: ClassDefs): Seq[xt.Expr] = {
    (args zip sym.info.paramInfoss.flatten) map {
      case (arg, ExprType(_)) => xt.Lambda(Seq(), extractTree(arg)).setPos(arg.sourcePos)
      case (arg, _) => extractTree(arg)
    }
  }

  def stripAnnotationsExceptStrictBV(tpe: xt.Type): xt.Type = tpe match {
    case xt.AnnotatedType(tp, flags) if flags.contains(xt.StrictBV) =>
      xt.AnnotatedType(stripAnnotationsExceptStrictBV(tp), Seq(xt.StrictBV))
    case xt.AnnotatedType(tp, _) =>
      stripAnnotationsExceptStrictBV(tp)
    case _ => tpe
  }

  // TODO: Review
  // TODO: Review
  // TODO: Review
  private def extractTree(tr: tpd.Tree)(using dctx: DefContext, cds: ClassDefs): xt.Expr = (tr match {
    // TODO: Some things like moduledef that are ignored
    case SingletonTypeTree(tree) => extractTree(tree)

    case ExLambda(vparams, rhs) =>
      val vds = vparams map (vd => xt.ValDef(
        FreshIdentifier(vd.symbol.name.toString),
        extractType(vd.tpt),
        annotationsOf(vd.symbol)
      ).setPos(vd.sourcePos))

      xt.Lambda(vds, extractTree(rhs)(using dctx.withNewVars((vparams zip vds).map {
        case (v, vd) => v.symbol -> (() => vd.toVariable)
      })))

    case Block(es, e) =>
      // TODO: Difference with scalac. See whether we need the same logic or not
      val b = extractBlock(es :+ e)
      xt.exprOps.flattenBlocks(b)

    case Try(body, cses, fin) =>
      val rb = extractTree(body)
      val rc = cses.map(extractMatchCase)
      xt.Try(rb, rc, if (fin == tpd.EmptyTree) None else Some(extractTree(fin)))

    case Return(e, _) => xt.Return(extractTree(e))

    case Apply(ex, Seq(arg)) if ex.symbol == defn.throwMethod =>
      xt.Throw(extractTree(arg))

    // TODO: Say must be put before "Inlined" extractor
    case ExAssertExpression(contract, oerr, isStatic) =>
      def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
      val contr = extractTree(contract)
      val body = contr match {
        // If we encounter an assert(false), we can generate a NoTree of Nothing for the body.
        // This is especially useful if this assert happens to be the last statement, as we may refine
        // the return type of the branch or the function to Nothing
        case xt.BooleanLiteral(false) =>
          xt.NoTree(xt.NothingType())
        case _ => xt.UnitLiteral()
      }
      xt.Assert(wrap(contr), oerr, body.setPos(tr.sourcePos))

    case ExRequiredExpression(contract, isStatic) =>
      def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
      xt.Require(wrap(extractTree(contract)), xt.UnitLiteral().setPos(tr.sourcePos))

    case ExReadsExpression(objs) =>
      xt.Reads(extractTree(objs), xt.UnitLiteral().setPos(tr.sourcePos))

    case ExModifiesExpression(objs) =>
      xt.Modifies(extractTree(objs), xt.UnitLiteral().setPos(tr.sourcePos))

    case ExEnsuredExpression(body, contract, isStatic) =>
      def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x

      val post = extractTree(contract)
      val b = extractTreeOrNoTree(body)

      xt.Ensuring(b, post match {
        case l: xt.Lambda => l.copy(body = wrap(l.body)).copiedFrom(l)
        case other =>
          val tpe = extractType(tr)
          val vd = xt.ValDef.fresh("res", tpe).setPos(post)
          xt.Lambda(Seq(vd), wrap(extractType(contract) match {
            case xt.BooleanType() => post
            case _ => xt.Application(other, Seq(vd.toVariable)).setPos(post)
          })).setPos(post)
      })

    case ExThrowingExpression(body, contract) =>
      val pred = extractTree(contract)
      val b = extractTreeOrNoTree(body)

      xt.Throwing(b, pred match {
        case l: xt.Lambda => l
        case other =>
          val tpe = extractType(exceptionSym.info)(using dctx, contract.sourcePos)
          val vd = xt.ValDef.fresh("res", tpe).setPos(other)
          xt.Lambda(Seq(vd), xt.Application(other, Seq(vd.toVariable)).setPos(other)).setPos(other)
      })

    case t @ ExHoldsWithProofExpression(body, ExMaybeBecauseExpressionWrapper(proof)) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.sourcePos)).setPos(tr.sourcePos)
      val p = extractTreeOrNoTree(proof)
      val and = xt.And(p, vd.toVariable).setPos(tr.sourcePos)
      val post = xt.Lambda(Seq(vd), and).setPos(tr.sourcePos)
      val b = extractTreeOrNoTree(body)
      xt.Ensuring(b, post).setPos(post)

    case t @ ExHoldsExpression(body) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.sourcePos)).setPos(tr.sourcePos)
      val post = xt.Lambda(Seq(vd), vd.toVariable).setPos(tr.sourcePos)
      val b = extractTreeOrNoTree(body)
      xt.Ensuring(b, post).setPos(post)

/*
    case t @ ExHoldsBecause(body, proof) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.sourcePos)).setPos(tr.sourcePos)
      val post = xt.Lambda(Seq(vd),
        xt.And(Seq(extractTreeOrNoTree(proof), vd.toVariable)).setPos(tr.sourcePos)
      ).setPos(tr.sourcePos)
      xt.Ensuring(extractTreeOrNoTree(body), post).setPos(post)

    case t @ ExHoldsExpression(body, proof) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.sourcePos)).setPos(tr.sourcePos)
      val post = xt.Lambda(Seq(vd),
        xt.And(Seq(extractTree(proof), vd.toVariable)).setPos(tr.sourcePos)
      ).setPos(tr.sourcePos)
      xt.Ensuring(extractTreeOrNoTree(body), post).setPos(post)

    case t @ ExHoldsExpression(body) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.sourcePos)).setPos(tr.sourcePos)
      val post = xt.Lambda(Seq(vd), vd.toVariable).setPos(tr.sourcePos)
      val b = extractTreeOrNoTree(body)
      xt.Ensuring(b, post).setPos(post)
*/
    // If the because statement encompasses a holds statement
    case t @ ExBecauseExpression(ExHoldsExpression(body), proof) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.sourcePos)).setPos(tr.sourcePos)
      val p = extractTree(proof)
      val and = xt.And(p, vd.toVariable).setPos(tr.sourcePos)
      val post = xt.Lambda(Seq(vd), and).setPos(tr.sourcePos)
      val b = extractTreeOrNoTree(body)
      xt.Ensuring(b, post).setPos(post)

    case t @ ExComputesExpression(body, expected) =>
      val tpe = extractType(body)
      val vd = xt.ValDef.fresh("holds", tpe).setPos(tr.sourcePos)
      val post = xt.Lambda(Seq(vd),
        xt.Equals(vd.toVariable, extractTreeOrNoTree(expected)).setPos(tr.sourcePos)
      ).setPos(tr.sourcePos)
      xt.Ensuring(extractTreeOrNoTree(body), post).setPos(post)

    case ExPasses(in, out, cases) =>
      val ine = extractTree(in)
      val oute = extractTree(out)
      val rc = cases.map(extractMatchCase)

      xt.Passes(ine, oute, rc)

    case t @ ExBigLengthExpression(input) =>
      xt.StringLength(extractTree(input))

    case t @ ExBigSubstringExpression(input, start) =>
      val in = extractTree(input)
      val st = extractTree(start)
      val vd = xt.ValDef.fresh("s", xt.StringType().setPos(t.sourcePos), true).setPos(t.sourcePos)
      xt.Let(vd, in, xt.SubString(vd.toVariable, st, xt.StringLength(vd.toVariable).setPos(t.sourcePos)).setPos(t.sourcePos))

    case t @ ExBigSubstring2Expression(input, start, end) =>
      val in = extractTree(input)
      val st = extractTree(start)
      val en = extractTree(end)
      xt.SubString(in, st, en)

    case ExArrayLiteral(tpe, args) =>
      xt.FiniteArray(extractSeq(args), extractType(tpe)(using dctx, tr.sourcePos))

    case s @ ExCaseObject(sym) =>
      extractType(s) match {
        case ct: xt.ClassType => xt.ClassConstructor(ct, Seq.empty)
        case tpe => outOfSubsetError(tr, "Unexpected class constructor type: " + tpe)
      }

    case ExTuple(args) =>
      xt.Tuple(args.map(extractTree))

    case ExOldExpression(e) => xt.Old(extractTree(e))

    case ExSnapshotExpression(e) => xt.Snapshot(extractTree(e))

    case ExFreshCopyExpression(t) => xt.FreshCopy(extractTree(t))

    case ExErrorExpression(str, tpt) => xt.Error(extractType(tpt), str)

    case ExTupleExtract(tuple, i) =>
      xt.TupleSelect(extractTree(tuple), i)

    /**
     * XLang Extractors
     */

    case a @ Assign(id @ Ident(_), rhs) =>
      // TODO: Review
      dctx.mutableVars.get(id.symbol) match {
        case Some(fun) =>
          xt.Assignment(fun().setPos(id.sourcePos), extractTree(rhs))

        case None => id.tpe match {
          case TermRef(tt: ThisType, _) =>
            val thiss = extractType(tt)(using dctx, id.sourcePos) match {
              case ct: xt.ClassType => xt.This(ct)
              case lct: xt.LocalClassType => xt.LocalThis(lct)
            }
            xt.FieldAssignment(thiss.setPos(id.sourcePos), getIdentifier(id.symbol), extractTree(rhs))

          case _ =>
            outOfSubsetError(a, "Undeclared variable.")
        }
      }

    // TODO: Review
    // TODO: Review
    // TODO: Review
    case a @ ExAssign(sym, lhs, rhs) =>
      import dotty.tools.dotc.core.NameOps._
      // TODO: "standardize" what a "true field" means
      val isTrueField = (sym is CaseAccessor) || (sym is ParamAccessor)
      if (isTrueField) {
        xt.FieldAssignment(extractTree(lhs), getIdentifier(sym), extractTree(rhs))
      } else {
        val setterName = sym.underlyingSymbol.name.asTermName.setterName
        val d = sym.owner.info.decl(setterName)
        val setterSymbol = d.suchThat(_.info.firstParamTypes.nonEmpty).symbol

        extractType(lhs)(using dctx.setResolveTypes(true)) match {
          case ct: xt.ClassType =>
            xt.MethodInvocation(extractTree(lhs), getIdentifier(setterSymbol), Seq.empty, Seq(extractTree(rhs))).setPos(a.sourcePos)

          case lct: xt.LocalClassType =>
            val lcd = dctx.localClasses(lct.id)
            val id = getIdentifier(setterSymbol)
            val funType = xt.FunctionType(Seq(extractType(rhs)), xt.UnitType())
            xt.LocalMethodInvocation(
              extractTree(lhs),
              xt.ValDef(id, funType).toVariable,
              Seq.empty,
              Seq.empty,
              Seq(extractTree(rhs))
            ).setPos(a.sourcePos)
        }
      }

    case wh @ ExWhile(cond, body, invOpt, weakInvOpt, inline, opaque) =>
      val inlineFlag = if (inline) Some(xt.InlineOnce) else None
      val opaqueFlag = if (opaque) Some(xt.Opaque) else None
      val flags = inlineFlag.toSeq ++ opaqueFlag
      xt.While(extractTree(cond), extractTree(body), invOpt.map(extractTree), weakInvOpt.map(extractTree), flags)

    // TODO: check if can be removed
    case ExUnwrapped(tree) if tree ne tr => extractTree(tree)

    case ExBigIntLiteral(Literal(cnst)) =>
      xt.IntegerLiteral(BigInt(cnst.stringValue))

    case ExBigIntLiteral(_) => outOfSubsetError(tr, "Only literal arguments are allowed for BigInt.")

    case ExIntToBigInt(t) => extractTree(t) match {
      case xt.Int32Literal(n) => xt.IntegerLiteral(BigInt(n))
      case _ => outOfSubsetError(tr, "Conversion from Int to BigInt")
    }

    case ExIntToBV(FrontendBVKind(signed, size), tree) =>
      extractTree(tree) match {
        case xt.Int32Literal(n)
          if !signed && 0 <= n && BigInt(n) < BigInt(2).pow(size) =>

          xt.BVLiteral(signed, BigInt(n), size)
        case xt.Int32Literal(n)
          if signed && -(BigInt(2).pow(size-1)) <= BigInt(n) && BigInt(n) < BigInt(2).pow(size-1) =>

          xt.BVLiteral(signed, BigInt(n), size)
        case _ => outOfSubsetError(tr, "`intToBV` may only be used on `Int` literals (in the right range)")
      }

    case ExIntToBV(typ, tree) =>
      outOfSubsetError(tr, s"`intToBV` cannot be instantiated on non-bitvector type $typ")

    case ExBigIntToBV(signed, size, tree) =>
      extractTree(tree) match {
        case xt.IntegerLiteral(n)
          if signed && 0 <= n && n < BigInt(2).pow(size) =>

          xt.BVLiteral(signed, n, size)
        case xt.IntegerLiteral(n)
          if signed && -(BigInt(2).pow(size-1)) <= n && n < BigInt(2).pow(size-1) =>

          xt.BVLiteral(signed, n, size)
        case _ => outOfSubsetError(tr, "`bigIntToBV` implicit may only be used on `BigInt` literals (in the right range)")
      }

    case ExMaxBV(signed, size) =>
      if (signed) xt.BVLiteral(signed, (BigInt(2) pow (size - 1)) - 1, size)
      else xt.BVLiteral(signed,  (BigInt(2) pow size) - 1, size)

    case ExMinBV(signed, size) =>
      if (signed) xt.BVLiteral(signed, -(BigInt(2) pow (size - 1)), size)
      else xt.BVLiteral(signed, BigInt(0), size)

    case ExFromByte(tree) => extractTree(tree)
    case ExFromShort(tree) => extractTree(tree)
    case ExFromInt(tree) => extractTree(tree)
    case ExFromLong(tree) => extractTree(tree)

    case ExWrapping(tree) =>
      val body = extractTree(tree)(using dctx.setWrappingArithmetic(true))
      xt.Annotated(body, Seq(xt.Wrapping))

    case ExRealLiteral(args) => args.map(extractTree) match {
      case Seq(xt.IntegerLiteral(n), xt.IntegerLiteral(d)) => xt.FractionLiteral(n, d)
      case Seq(xt.IntegerLiteral(n)) => xt.FractionLiteral(n, 1)
      case _ => outOfSubsetError(tr, "Real not built from literals")
    }

    case ExInt8Literal(v)  => xt.Int8Literal(v)
    case ExInt16Literal(v) => xt.Int16Literal(v)
    case ExInt32Literal(v) => xt.Int32Literal(v)
    case ExInt64Literal(v) => xt.Int64Literal(v)
    case ExUnitLiteral() => xt.UnitLiteral()
    case ExBooleanLiteral(v) => xt.BooleanLiteral(v)
    case ExCharLiteral(c) => xt.CharLiteral(c)
    case ExStringLiteral(s) => xt.StringLiteral(s)

    case ExEffectivelyLiteral(lit) => extractTree(lit)

    case ExIdentity(body) => extractTree(body)

    case Apply(TypeApply(ExSymbol("scala", "Predef$", "locally"), _), Seq(body)) =>
      extractTree(body)

    case ExTyped(ExSymbol("scala", "Predef$", "$qmark$qmark$qmark" | "???"), tpe) =>
      xt.NoTree(extractType(tpe))

    case ExSymbol("scala", "Predef$", "$qmark$qmark$qmark" | "???") => xt.NoTree(extractType(tr))

    case Typed(e, _) =>
      extractTree(e)

    // TODO: In scalac, two cases dealing with identifiers (one of which has to do with case objects)
    //  Here, the identifier handling is lighter, we are maybe missing some cases
    //  Also, find a way to get rid of ExExtensionMethod

    case Inlined(call, members, body) =>
      def rec(expr: xt.Expr): xt.Expr = expr match {
        case xt.Let(vd, e, b) => xt.Let(vd, e, rec(b)).copiedFrom(expr)
        case xt.LetRec(fds, b) => xt.LetRec(fds, rec(b)).copiedFrom(expr)
        case xt.Decreases(_, _) =>
          outOfSubsetError(tr, "No measure should be specified on inlined functions")
        case xt.Require(pre, b) =>
          xt.Assert(pre, Some("Inlined precondition"), rec(b)).copiedFrom(expr)
        case xt.Ensuring(b, xt.Lambda(Seq(vd), post)) =>
          xt.Let(vd, rec(b), xt.Assume(post, vd.toVariable).copiedFrom(expr)).copiedFrom(expr)
        case xt.NoTree(_) =>
          outOfSubsetError(tr, "Can't inline empty body")
        case _ =>
          xt.Annotated(expr, Seq(xt.DropVCs))
      }

      rec(extractBlock(members :+ body))

    case ExChooseExpression(tpt, pred) =>
      extractTree(pred) match {
        case xt.Lambda(Seq(vd), body) => xt.Choose(vd, body)
        // TODO: This part is not in scalac
        case e => extractType(tpt) match {
          case xt.FunctionType(Seq(argType), xt.BooleanType()) =>
            val vd = xt.ValDef.fresh("x", argType, true).setPos(pred.sourcePos)
            xt.Choose(vd, xt.Application(e, Seq(vd.toVariable)).setPos(pred.sourcePos))
          case _ => outOfSubsetError(tr, "Expected choose to take a function-typed predicate")
        }
      }

    case ExSwapExpression(array1, index1, array2, index2) =>
      xt.Swap(extractTree(array1), extractTree(index1), extractTree(array2), extractTree(index2))

    case ExForallExpression(fun) =>
      extractTree(fun) match {
        case l: xt.Lambda => xt.Forall(l.params, l.body).setPos(l)
        case pred => extractType(fun) match {
          case xt.FunctionType(from, to) =>
            val args = from.map(tpe => xt.ValDef(FreshIdentifier("x", true), tpe).setPos(pred))
            xt.Forall(args, xt.Application(pred, args.map(_.toVariable)).setPos(pred))
          case _ =>
            outOfSubsetError(tr, "Unsupported forall definition: " + tr)
        }
      }

    case ExMutableMapWithDefault(tptFrom, tptTo, default) =>
      xt.MutableMapWithDefault(extractType(tptFrom), extractType(tptTo), extractTree(default))

    case ExFiniteMap(tptFrom, tptTo, args) =>
      val to = extractType(tptTo)
      // TODO: Different from Scalac
      val pairs = extractSeq(args) map {
        case xt.Tuple(Seq(key, value)) => key -> value
        case e => (xt.TupleSelect(e, 1).setPos(e), xt.TupleSelect(e, 2).setPos(e))
      }

      val somePairs = pairs.map { case (key, value) =>
        key -> xt.ClassConstructor(
          xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(value),
          Seq(value)
        ).setPos(value)
      }

      val dflt = xt.ClassConstructor(
        xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(tr.sourcePos),
        Seq.empty
      ).setPos(tr.sourcePos)

      val optTo = xt.ClassType(getIdentifier(optionSymbol), Seq(to))
      xt.FiniteMap(somePairs, dflt, extractType(tptFrom), optTo)

    case ExFiniteSet(tpt, args) =>
      xt.FiniteSet(extractSeq(args), extractType(tpt))

    case ExFiniteBag(tpt, args) =>
      // TODO: Different from Scalac
      xt.FiniteBag(extractSeq(args).map {
        case xt.Tuple(Seq(key, value)) => key -> value
        case e => (xt.TupleSelect(e, 1).setPos(e), xt.TupleSelect(e, 2).setPos(e))
      }, extractType(tpt))

    // TODO: review
    case ExClassConstruction(tpe, args) => extractType(tpe)(using dctx, tr.sourcePos) match {
      case lct: xt.LocalClassType => xt.LocalClassConstructor(lct, args map extractTree)
      case ct: xt.ClassType => xt.ClassConstructor(ct, args map extractTree)
      case tt: xt.TupleType => xt.Tuple(args map extractTree)
      case _ => outOfSubsetError(tr, "Unexpected constructor " + tr.show + "   " + tpe.show)
    }

    case ExNot(e)    => xt.Not(extractTree(e))
    case ExUMinus(e) => injectCast(xt.UMinus.apply)(e)
    case ExBVNot(e)  => injectCast(xt.BVNot.apply)(e)

    case ExNotEquals(l, r) => xt.Not(((extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
      case (bi @ xt.BVLiteral(_, _, _), _, e, xt.IntegerType()) => xt.Equals(xt.IntegerLiteral(bi.toBigInt).setPos(l.sourcePos), e)
      case (e, xt.IntegerType(), bi @ xt.BVLiteral(_, _, _), _) => xt.Equals(e, xt.IntegerLiteral(bi.toBigInt).setPos(r.sourcePos))

      case (l2, StrictBVType(signed, size), xt.IntegerLiteral(value), _) =>
        xt.Equals(l2, xt.BVLiteral(signed, value, size).setPos(r.sourcePos))
      case (l2, StrictBVType(signed, size), xt.Int32Literal(value), _) =>
        xt.Equals(l2, xt.BVLiteral(signed, BigInt(value), size).setPos(r.sourcePos))
      case (xt.IntegerLiteral(value), _, r2, StrictBVType(signed, size)) =>
        xt.Equals(xt.BVLiteral(signed, value, size).setPos(l.sourcePos), r2)
      case (xt.Int32Literal(value), _, r2, StrictBVType(signed, size)) =>
        xt.Equals(xt.BVLiteral(signed, BigInt(value), size).setPos(l.sourcePos), r2)

      case (l2, tpeL @ StrictBVType(_, _), r2, tpeR) =>
        if (tpeL == tpeR) xt.Equals(l2, r2)
        else outOfSubsetError(tr, "Bitvectors can only be compared with bitvectors of the same type.")
      case (l2, tpeL, r2, tpeR @ StrictBVType(_, _)) =>
        if (tpeL == tpeR) xt.Equals(l2, r2)
        else outOfSubsetError(tr, "Bitvectors can only be compared with bitvectors of the same type.")

      case _ => injectCasts(xt.Equals.apply)(l, r)
    }).setPos(tr.sourcePos))

    case ExEquals(l, r) => (extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
      case (bi @ xt.BVLiteral(_, _, _), _, e, xt.IntegerType()) => xt.Equals(xt.IntegerLiteral(bi.toBigInt).setPos(l.sourcePos), e)
      case (e, xt.IntegerType(), bi @ xt.BVLiteral(_, _, _), _) => xt.Equals(e, xt.IntegerLiteral(bi.toBigInt).setPos(r.sourcePos))

      case (l2, StrictBVType(signed, size), xt.IntegerLiteral(value), _) =>
        xt.Equals(l2, xt.BVLiteral(signed, value, size).setPos(r.sourcePos))
      case (l2, StrictBVType(signed, size), xt.Int32Literal(value), _) =>
        xt.Equals(l2, xt.BVLiteral(signed, BigInt(value), size).setPos(r.sourcePos))
      case (xt.IntegerLiteral(value), _, r2, StrictBVType(signed, size)) =>
        xt.Equals(xt.BVLiteral(signed, value, size).setPos(l.sourcePos), r2)
      case (xt.Int32Literal(value), _, r2, StrictBVType(signed, size)) =>
        xt.Equals(xt.BVLiteral(signed, BigInt(value), size).setPos(l.sourcePos), r2)

      case (l2, tpeL @ StrictBVType(_, _), r2, tpeR) =>
        if (tpeL == tpeR) xt.Equals(l2, r2)
        else outOfSubsetError(tr, "Bitvectors can only be compared with bitvectors of the same type.")
      case (l2, tpeL, r2, tpeR @ StrictBVType(_, _)) =>
        if (tpeL == tpeR) xt.Equals(l2, r2)
        else outOfSubsetError(tr, "Bitvectors can only be compared with bitvectors of the same type.")

      case _ => injectCasts(xt.Equals.apply)(l, r)
    }

    /*
    case Select(e, nme.UNARY_+) => injectCast(e => e)(e)
    case Select(e, nme.UNARY_!) => xt.Not(extractTree(e))
    case Select(e, nme.UNARY_-) => injectCast(xt.UMinus.apply)(e)
    case Select(e, nme.UNARY_~) => injectCast(xt.BVNot.apply)(e)

    case Apply(Select(l, nme.NE), Seq(r)) => xt.Not(((extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
      case (lit @ xt.BVLiteral(_, _, _), _, e, xt.IntegerType()) => xt.Equals(xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit), e)
      case (e, xt.IntegerType(), lit @ xt.BVLiteral(_, _, _), _) => xt.Equals(e, xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit))
      case _ => injectCasts(xt.Equals.apply)(l, r)
    }).setPos(tr.sourcePos))

    case Apply(Select(l, nme.EQ), Seq(r)) => (extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
      case (lit @ xt.BVLiteral(_, _, _), _, e, xt.IntegerType()) => xt.Equals(xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit), e)
      case (e, xt.IntegerType(), lit @ xt.BVLiteral(_, _, _), _) => xt.Equals(e, xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit))
      case _ => injectCasts(xt.Equals.apply)(l, r)
    }
    */

    case If(t1,t2,t3) =>
      xt.IfExpr(extractTree(t1), extractTree(t2), extractTree(t3))

    // TODO: verify
    case TypeApply(s @ Select(t, _), Seq(tpt)) if s.symbol == defn.Any_asInstanceOf =>
      extractType(tpt) match {
        case ct: xt.ClassType => xt.AsInstanceOf(extractTree(t), ct)
        case _ =>
          // XXX @nv: dotc generates spurious `asInstanceOf` casts for now, se
          //          we will have to rely on later type checks within Stainless
          //          to catch issues stemming from casts we ignored here.
          // outOfSubsetError(tr, "asInstanceOf can only cast to class types")
          extractTree(t)
      }

    case TypeApply(s @ Select(t, _), Seq(tpt)) if s.symbol == defn.Any_isInstanceOf =>
      extractType(tpt) match {
        case ct: xt.ClassType => xt.IsInstanceOf(extractTree(t), ct)
        case _ => outOfSubsetError(tr, "isInstanceOf can only be used with class types")
      }

    case Match(scrut, cases) =>
      xt.MatchExpr(extractTree(scrut), cases.map(extractMatchCase))

    case t @ This(_) =>
      extractType(t) match {
        case ct: xt.ClassType => xt.This(ct)
        case lct: xt.LocalClassType => xt.LocalThis(lct)
        case _ => outOfSubsetError(t, "Invalid usage of `this`")
      }

    case s @ Super(_, _) =>
      extractType(s) match {
        case ct: xt.ClassType => xt.Super(ct)
        case lct: xt.LocalClassType => xt.Super(lct.toClassType)
        case _ => outOfSubsetError(s, s"Invalid usage of `super`")
      }

    case ExArrayFill(baseType, length, defaultValue) =>
      val lengthRec = extractTree(length)
      val defaultValueRec = extractTree(defaultValue)
      xt.LargeArray(Map.empty, extractTree(defaultValue), extractTree(length), extractType(baseType))

    case ExArrayUpdate(array, index, newValue) =>
      xt.ArrayUpdate(extractTree(array), extractTree(index), extractTree(newValue))

    case ExArrayUpdated(array, index, newValue) =>
      xt.ArrayUpdated(extractTree(array), extractTree(index), extractTree(newValue))

    case ExArrayApplyBV(array, bvType, index) => bvType match {
      case FrontendBVType(signed, size) =>
        xt.ArraySelect(
          extractTree(array),
          toSigned(extractTree(index), signed, size, 32)
        )
      // TODO: Scalac says FrontenBVType, but with some tests, we have FrontendBVKind...
      case FrontendBVKind(signed, size) =>
        xt.ArraySelect(
          extractTree(array),
          toSigned(extractTree(index), signed, size, 32)
        )
      case tpe =>
        outOfSubsetError(bvType, s"ArrayIndexing implicit must be used on a BitVector type (found $tpe instead)")
    }

    case ExArrayLength(array) =>
      xt.ArrayLength(extractTree(array))

    case ExArrayApply(array, index) => xt.ArraySelect(extractTree(array), extractTree(index))

    case ExListLiteral(tpt, args) =>
      val tpe = extractType(tpt)
      val cons = xt.ClassType(getIdentifier(consSymbol), Seq(tpe))
      val nil  = xt.ClassType(getIdentifier(nilSymbol),  Seq(tpe))
      extractSeq(args).foldRight(xt.ClassConstructor(nil, Seq.empty).setPos(tr.sourcePos)) {
        case (e, ls) => xt.ClassConstructor(cons, Seq(e, ls)).setPos(e)
      }

    case ExImplies(lhs, rhs) =>
      xt.Implies(extractTree(lhs), extractTree(rhs))

    case ExSplitAnd(lhs, rhs) =>
      xt.SplitAnd(extractTree(lhs), extractTree(rhs))

    case app @ Apply(tree, args) if defn.isFunctionType(tree.tpe) =>
      xt.Application(extractTree(tree), args map extractTree).setPos(app.sourcePos)

    case NamedArg(name, arg) => extractTree(arg)

    case ex @ ExIdentifier(sym, tpt) if dctx.vars contains sym => dctx.vars(sym)().setPos(ex.sourcePos)
    case ex @ ExIdentifier(sym, tpt) if dctx.mutableVars contains sym => dctx.mutableVars(sym)().setPos(ex.sourcePos)

    /*
    // TODO: No
    case call@ExCall(_, extMethSym, _, _) if (extMethSym.name is NameKinds.ExtMethName) =>
      val clsSym = extMethSym.denot.owner.asClass
      val clsDef = cds.defs.find(_.symbol eq clsSym).get
      val template = clsDef.rhs.asInstanceOf[tpd.Template]
      val methDef = template.body.collectFirst {
        case d@DefDef(nme, _, _, _) if nme == extMethSym.name => d
      }.get
      val inl = new typer.Inliner(call, methDef.rhs)
      val res = inl.inlined(call)
      extractTree(res.asInstanceOf[tpd.Inlined].expansion)
    */
    // TODO: Review. This case can occur if there is a "naked" Ident(myField)
    case ExThisCall(tt, sym, tps, args) =>
//      val id = if (sym is ParamAccessor) getParam(sym) else getIdentifier(sym)
      val id = getIdentifier(sym)
      // TODO: review
      extractType(tt)(using dctx, tr.sourcePos) match {
        case ct: xt.ClassType =>
          val isField = (sym is ParamAccessor) || (sym is CaseAccessor)
          val isMethod = (sym is Method) /*|| (sym is Accessor)*/ || !isField
          val thiss = xt.This(ct).setPos(tr.sourcePos)
          if (isMethod)
            xt.MethodInvocation(thiss, id, tps map extractType, extractArgs(sym, args)).setPos(tr.sourcePos)
          else args match {
            case Seq() if sym is ParamAccessor => // TODO: What about CaseAccessor (ditto for Scalac)???
              xt.ClassSelector(thiss, id).setPos(tr.sourcePos)
            case _ =>
              outOfSubsetError(tr, s"Unexpected call: $tr")
          }

        case lct: xt.LocalClassType =>
          val isField = (sym is ParamAccessor) || (sym is CaseAccessor)
          val isMethod = (sym is Method) /*|| (sym is Accessor)*/ || !isField
          val thiss = xt.LocalThis(lct).setPos(tr.sourcePos)
          val lcd = dctx.localClasses(lct.id)
          if (isMethod) {
            val fd = lcd.methods.find(_.id == id).get
            xt.LocalMethodInvocation(
              thiss,
              xt.ValDef(id, xt.FunctionType(fd.params.map(_.tpe), fd.returnType)).toVariable.setPos(tr.sourcePos),
              fd.tparams.map(_.tp),
              tps.map(extractType),
              extractArgs(sym, args)
            ).setPos(tr.sourcePos)
          } else args match {
            case Seq() if sym is ParamAccessor => // TODO: What about CaseAccessor (ditto for Scalac)???
              val field = lcd.fields.collectFirst { case vd @ xt.ValDef(`id`, _, _) => vd }
              xt.LocalClassSelector(thiss, id, field.map(_.tpe).getOrElse(xt.Untyped))
            case _ =>
              outOfSubsetError(tr, s"Unexpected call: $tr")
          }
      }

    case ExCastCall(expr, from, to) =>
      // Double check that we are dealing with regular integer types
      val xt.BVType(true, size) = extractType(from)(using dctx, NoSourcePosition)
      val newType @ xt.BVType(true, newSize) = extractType(to)(using dctx, NoSourcePosition)
      if (size > newSize) xt.BVNarrowingCast(extractTree(expr), newType)
      else                xt.BVWideningCast(extractTree(expr), newType)

    // TODO: Explain
    case ExCbnCall(res) =>
//      println(s"$res        ${res.show}")
      val rec = extractTree(res)
//      println(s"  ~> $rec")
      rec
/*
    // TODO: Explain
    // TODO: Verify how things behave with type & term parameters
    // TODO: Say must be before ExCall
    case ExExtensionMethodCall(res) =>
//      println(s"${tr.show}")
//      println(s"   ~> ${res.show}")
      val rec = extractTree(res)
//      println(s"       ~> $rec")
      rec
*/
//    case c@ExExtensionMethodCall(thiss, sym, tps, args) =>
//      val res = extractCall(c, Some(thiss), sym, tps, args)
//      res
    case c@ExCall(rec, sym, tps, args) =>
      extractCall(c, rec, sym, tps, args)

    // default behaviour is to complain :)
    case _ => outOfSubsetError(tr, s"Stainless does not support expression: `$tr`")
  }).ensurePos(tr.sourcePos)

  // TODO: Can be put back
  private def extractCall(tr: tpd.Tree, rec: Option[tpd.Tree], sym: Symbol, tps: Seq[tpd.Tree], args: Seq[tpd.Tree])(using dctx: DefContext, cds: ClassDefs): xt.Expr = rec match {
    // TODO: Can be removed
    /*
    case Some(Select(rec @ Super(_, _), m)) if (sym is Abstract) && m != nme.CONSTRUCTOR =>
      outOfSubsetError(tr.sourcePos, "Cannot issue a super call to an abstract method.")
    */
    // TODO: what about object method invocation? are these function invocation?
    case None if (sym.owner is ModuleClass) && (sym.owner is Case) =>
      val ct = extractType(sym.owner.thisType)(using dctx, tr.sourcePos).asInstanceOf[xt.ClassType]
      xt.MethodInvocation(
        xt.This(ct).setPos(tr.sourcePos),
        getIdentifier(sym),
        tps map extractType,
        args map extractTree
      ).setPos(tr.sourcePos)

    case None =>
      dctx.localFuns.get(sym) match {
        case None =>
          xt.FunctionInvocation(getIdentifier(sym), tps map extractType, extractArgs(sym, args)).setPos(tr.sourcePos)
        case Some((id, tparams, tpe)) =>
          xt.ApplyLetRec(id, tparams.map(_.tp), tpe, tps map extractType, extractArgs(sym, args)).setPos(tr.sourcePos)
      }

    case Some(lhs) => stripAnnotationsExceptStrictBV(extractType(lhs)(using dctx.setResolveTypes(true))) match {
      // TODO:
      case ct: xt.ClassType =>
        // TODO: What about "abstract field" ???
        val isField = (sym is ParamAccessor) || (sym is CaseAccessor)
        val isMethod = (sym is Method) || /*(sym is Accessor) ||*/ !isField

        if (isMethod) xt.MethodInvocation(
          extractTree(lhs),
          getIdentifier(sym),
          tps.map(extractType),
          extractArgs(sym, args)
        ).setPos(tr.sourcePos) else args match {
          case Seq() if sym is ParamAccessor => // TODO: What about CaseAccessor (ditto for Scalac)???
            xt.ClassSelector(extractTree(lhs), getIdentifier(sym)).setPos(tr.sourcePos)
          case _ =>
            outOfSubsetError(tr, s"Unexpected call: $tr")
        }
      //          val id = if (sym is ParamAccessor) getParam(sym) else getIdentifier(sym)
      //          xt.MethodInvocation(extractTree(lhs), id, tps map extractType, extractArgs(sym, args)).setPos(tr.sourcePos)

      case lct: xt.LocalClassType =>
        // TODO: What about "abstract field" ???
        val isField = (sym is ParamAccessor) || (sym is CaseAccessor)
        val isMethod = (sym is Method) /*|| (sym is Accessor)*/ || !isField
        val lcd = dctx.localClasses(lct.id)
        val id = getIdentifier(sym)
        if (isMethod) {
          val fd = lcd.methods.find(_.id == id).get
          xt.LocalMethodInvocation(
            extractTree(lhs),
            xt.ValDef(id, xt.FunctionType(fd.params.map(_.tpe), fd.returnType)).toVariable,
            fd.tparams.map(_.tp),
            tps.map(extractType),
            extractArgs(sym, args)
          )
        } else args match {
          case Seq() if sym is ParamAccessor => // TODO: What about CaseAccessor (ditto for Scalac)???
            val field = lcd.fields.collectFirst { case vd @ xt.ValDef(`id`, _, _) => vd }
            xt.LocalClassSelector(extractTree(lhs), id, field.map(_.tpe).getOrElse(xt.Untyped))
          case _ =>
            outOfSubsetError(tr, "Unexpected call")
        }

      /*
      val lcd = dctx.localClasses(lct.id)

      val id = if (sym is ParamAccessor) getParam(sym) else getIdentifier(sym)
      val fd = lcd.methods.find(_.id == id).get

      xt.LocalMethodInvocation(
        extractTree(lhs),
        xt.ValDef(id, xt.FunctionType(fd.params.map(_.tpe), fd.returnType)).toVariable,
        fd.tparams.map(_.tp),
        tps.map(extractType),
        extractArgs(sym, args)
      ).setPos(tr.sourcePos)
      */
      case ft: xt.FunctionType =>
        xt.Application(extractTree(lhs), args.map(extractTree)).setPos(ft)

      case pi: xt.PiType =>
        xt.Application(extractTree(lhs), args.map(extractTree)).setPos(pi)

      case tpe => (tpe, sym.name.decode.toString, args) match {
        case (xt.StringType(), "+", Seq(rhs)) => xt.StringConcat(extractTree(lhs), extractTree(rhs))
        case (xt.IntegerType() | xt.BVType(_,_) | xt.RealType(), "+", Seq(rhs)) => injectCasts(xt.Plus.apply)(lhs, rhs)

        case (xt.SetType(_), "+",  Seq(rhs)) => xt.SetAdd(extractTree(lhs), extractTree(rhs))
        case (xt.SetType(_), "++", Seq(rhs)) => xt.SetUnion(extractTree(lhs), extractTree(rhs))
        case (xt.SetType(_), "&",  Seq(rhs)) => xt.SetIntersection(extractTree(lhs), extractTree(rhs))
        case (xt.SetType(_), "--", Seq(rhs)) => xt.SetDifference(extractTree(lhs), extractTree(rhs))
        case (xt.SetType(_), "subsetOf", Seq(rhs)) => xt.SubsetOf(extractTree(lhs), extractTree(rhs))
        case (xt.SetType(_), "contains", Seq(rhs)) => xt.ElementOfSet(extractTree(rhs), extractTree(lhs))
        case (xt.SetType(b), "isEmpty", Seq()) => xt.Equals(extractTree(lhs), xt.FiniteSet(Seq(), b))
        case (xt.SetType(b), "-", Seq(rhs)) => xt.SetDifference(extractTree(lhs), xt.FiniteSet(Seq(extractTree(rhs)), b).setPos(tr.sourcePos))

        case (xt.BagType(_), "+",   Seq(rhs)) => xt.BagAdd(extractTree(lhs), extractTree(rhs))
        case (xt.BagType(_), "++",  Seq(rhs)) => xt.BagUnion(extractTree(lhs), extractTree(rhs))
        case (xt.BagType(_), "&",   Seq(rhs)) => xt.BagIntersection(extractTree(lhs), extractTree(rhs))
        case (xt.BagType(_), "--",  Seq(rhs)) => xt.BagDifference(extractTree(lhs), extractTree(rhs))
        case (xt.BagType(_), "get", Seq(rhs)) => xt.MultiplicityInBag(extractTree(rhs), extractTree(lhs))

        case (xt.ArrayType(_), "apply",   Seq(rhs))          => xt.ArraySelect(extractTree(lhs), extractTree(rhs))
        case (xt.ArrayType(_), "length",  Seq())             => xt.ArrayLength(extractTree(lhs))
        case (xt.ArrayType(_), "updated", Seq(index, value)) => xt.ArrayUpdated(extractTree(lhs), extractTree(index), extractTree(value))
        case (xt.ArrayType(_), "update",  Seq(index, value)) => xt.ArrayUpdate(extractTree(lhs), extractTree(index), extractTree(value))
        case (xt.ArrayType(_), "clone",   Seq())             => extractTree(lhs)

        case (xt.MutableMapType(_, _), "apply", Seq(rhs)) =>
          xt.MutableMapApply(extractTree(lhs), extractTree(rhs))

        case (xt.MutableMapType(_, _), "update", Seq(key, value)) =>
          xt.MutableMapUpdate(extractTree(lhs), extractTree(key), extractTree(value))

        case (xt.MutableMapType(_, _), "updated", Seq(key, value)) =>
          xt.MutableMapUpdated(extractTree(lhs), extractTree(key), extractTree(value))

        case (xt.MutableMapType(_, _), "duplicate", Seq()) =>
          xt.MutableMapDuplicate(extractTree(lhs))

        case (xt.MapType(_, _), "get", Seq(rhs)) =>
          xt.MapApply(extractTree(lhs), extractTree(rhs))

        case (xt.MapType(_, xt.ClassType(_, Seq(to))), "apply", Seq(rhs)) =>
          val (l, r) = (extractTree(lhs), extractTree(rhs))
          val someTpe = xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.sourcePos)
          xt.Assert(
            xt.IsInstanceOf(xt.MapApply(l, r).setPos(tr.sourcePos), someTpe).setPos(tr.sourcePos),
            Some("Map undefined at this index"),
            xt.ClassSelector(
              xt.AsInstanceOf(xt.MapApply(l, r).setPos(tr.sourcePos), someTpe).setPos(tr.sourcePos),
              getIdentifier(someSymbol.info.decl(termName("v")).symbol)
            ).setPos(tr.sourcePos)
          )

        case (xt.MapType(_, xt.ClassType(_, Seq(to))), "isDefinedAt" | "contains", Seq(rhs)) =>
          xt.Not(xt.Equals(
            xt.MapApply(extractTree(lhs), extractTree(rhs)).setPos(tr.sourcePos),
            xt.ClassConstructor(
              xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(tr.sourcePos),
              Seq.empty
            ).setPos(tr.sourcePos)
          ).setPos(tr.sourcePos))

        case (xt.MapType(_, xt.ClassType(_, Seq(to))), "updated" | "+", Seq(key, value)) =>
          xt.MapUpdated(
            extractTree(lhs), extractTree(key),
            xt.ClassConstructor(
              xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.sourcePos),
              Seq(extractTree(value))
            ).setPos(tr.sourcePos)
          )

        // TODO: different
        case (xt.MapType(from, xt.ClassType(_, Seq(to))), "+", Seq(rhs)) =>
          val vd = xt.ValDef(FreshIdentifier("x", true), xt.TupleType(Seq(from, to)).setPos(tr.sourcePos)).setPos(tr.sourcePos)
          xt.Let(vd, extractTree(rhs), xt.MapUpdated(
            extractTree(lhs), xt.TupleSelect(vd.toVariable, 1).setPos(tr.sourcePos),
            xt.ClassConstructor(
              xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.sourcePos),
              Seq(xt.TupleSelect(vd.toVariable, 2).setPos(tr.sourcePos))
            ).setPos(tr.sourcePos)
          ).setPos(tr.sourcePos))

        case (xt.MapType(_, xt.ClassType(_, Seq(to))), "removed" | "-", Seq(key)) =>
          xt.MapUpdated(
            extractTree(lhs), extractTree(key),
            xt.ClassConstructor(
              xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(tr.sourcePos),
              Seq.empty
            ).setPos(tr.sourcePos)
          )

        case (xt.MapType(_, xt.ClassType(_, Seq(to))), "++", Seq(rhs)) =>
          extractTree(rhs) match {
            case xt.FiniteMap(pairs, default, keyType, valueType) =>
              pairs.foldLeft(extractTree(lhs)) { case (map, (k, v)) =>
                xt.MapUpdated(map, k, v).setPos(tr.sourcePos)
              }

            case _ => outOfSubsetError(tr, "Can't extract map union with non-finite map")
          }

        case (xt.MapType(_, xt.ClassType(_, Seq(to))), "--", Seq(rhs)) =>
          extractTree(rhs) match {
            case xt.FiniteSet(els, _) =>
              val none = xt.ClassConstructor(
                xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(tr.sourcePos),
                Seq.empty
              ).setPos(tr.sourcePos)

              els.foldLeft(extractTree(lhs)) { case (map, k) =>
                xt.MapUpdated(map, k, none).setPos(tr.sourcePos)
              }

            case _ => outOfSubsetError(tr, "Can't extract map diff with non-finite map")
          }


        case (xt.MapType(_, xt.ClassType(_, Seq(to))), "getOrElse", Seq(key, orElse)) =>
          xt.MethodInvocation(
            xt.MapApply(extractTree(lhs), extractTree(key)).setPos(tr.sourcePos),
            getIdentifier(optionSymbol.info.decl(termName("getOrElse")).symbol),
            Seq.empty,
            Seq(xt.Lambda(Seq(), extractTree(orElse)).setPos(tr.sourcePos))
          )

        case (StrictBVType(_, _), "unary_~",  Seq())    => xt.BVNot(extractTree(lhs))
        case (StrictBVType(_, _), "unary_-",  Seq())    => xt.UMinus(extractTree(lhs))
        case (StrictBVType(_, _), "+",        Seq(rhs)) => xt.Plus(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "-",        Seq(rhs)) => xt.Minus(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "*",        Seq(rhs)) => xt.Times(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "%",        Seq(rhs)) => xt.Remainder(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "mod",      Seq(rhs)) => xt.Modulo(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "/",        Seq(rhs)) => xt.Division(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), ">",        Seq(rhs)) => xt.GreaterThan(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), ">=",       Seq(rhs)) => xt.GreaterEquals(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "<",        Seq(rhs)) => xt.LessThan(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "<=",       Seq(rhs)) => xt.LessEquals(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "|",        Seq(rhs)) => xt.BVOr(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "&",        Seq(rhs)) => xt.BVAnd(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "^",        Seq(rhs)) => xt.BVXor(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), "<<",       Seq(rhs)) => xt.BVShiftLeft(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), ">>",       Seq(rhs)) => xt.BVAShiftRight(extractTree(lhs), extractTree(rhs))
        case (StrictBVType(_, _), ">>>",      Seq(rhs)) => xt.BVLShiftRight(extractTree(lhs), extractTree(rhs))

        case (StrictBVType(signed, size), "widen",  Seq()) => tps match {
          case Seq(FrontendBVType(signed2, size2)) =>
            if (signed2 != signed) outOfSubsetError(tr, "Method `widen` must be used with a bitvector type of the same sign")
            else if (size2 <= size) outOfSubsetError(tr, "Method `widen` must be used with a bitvector type of a larger size")
            else xt.BVWideningCast(extractTree(lhs), xt.BVType(signed2, size2))
        }
        case (StrictBVType(signed, size), "narrow",  Seq()) => tps match {
          case Seq(FrontendBVType(signed2, size2)) =>
            if (signed2 != signed) outOfSubsetError(tr, "Method `narrow` must be used with a bitvector type of the same sign")
            else if (size2 >= size) outOfSubsetError(tr, "Method `narrow` must be used with a bitvector type of a smaller size")
            else xt.BVNarrowingCast(extractTree(lhs), xt.BVType(signed2, size2))
        }

        case (StrictBVType(signed, size), "toSigned",  Seq()) => tps match {
          case Seq(FrontendBVType(signed2, size2)) =>
            if (signed) outOfSubsetError(tr, "Method `toSigned` must be used on unsigned bitvectors")
            else if (!signed2) outOfSubsetError(tr, "Method `toSigned` must be instantiated with a signed bitvector type")
            else if (size != size2) outOfSubsetError(tr, "Method `toSigned` must be instantiated with a signed bitvector type of the same size as the original bitvector")
            else xt.BVUnsignedToSigned(extractTree(lhs))
          case _ =>
            outOfSubsetError(tr, "Method `toSigned` must be instantiated with a signed bitvector type of the same size as the original bitvector")
        }
        case (StrictBVType(signed, size), "toUnsigned",  Seq()) => tps match {
          case Seq(FrontendBVType(signed2, size2)) =>
            if (!signed) outOfSubsetError(tr, "Method `toUnsigned` must be used on signed bitvectors")
            else if (signed2) outOfSubsetError(tr, "Method `toUnsigned` must be instantiated with a unsigned bitvector type")
            else if (size != size2) outOfSubsetError(tr, "Method `toUnsigned` must be instantiated with a unsigned bitvector type of the same size as the original bitvector")
            else xt.BVSignedToUnsigned(extractTree(lhs))
          case _ =>
            outOfSubsetError(tr, "Method `toSigned` must be instantiated with a signed bitvector type of the same size as the original bitvector")
        }

        case (StrictBVType(signed, size), "toByte",  Seq()) =>
          toSigned(extractTree(lhs), signed, size, 8)
        case (StrictBVType(signed, size), "toShort",  Seq()) =>
          toSigned(extractTree(lhs), signed, size, 16)
        case (StrictBVType(signed, size), "toInt",  Seq()) =>
          toSigned(extractTree(lhs), signed, size, 32)
        case (StrictBVType(signed, size), "toLong",  Seq()) =>
          toSigned(extractTree(lhs), signed, size, 64)

        case (_, "unary_+", Seq()) => injectCast(e => e)(lhs)
        case (_, "-",   Seq(rhs)) => injectCasts(xt.Minus.apply)(lhs, rhs)
        case (_, "*",   Seq(rhs)) => injectCasts(xt.Times.apply)(lhs, rhs)
        case (_, "%",   Seq(rhs)) => injectCasts(xt.Remainder.apply)(lhs, rhs)
        case (_, "mod", Seq(rhs)) => xt.Modulo(extractTree(lhs), extractTree(rhs))
        case (_, "/",   Seq(rhs)) => injectCasts(xt.Division.apply)(lhs, rhs)
        case (_, ">",   Seq(rhs)) => injectCasts(xt.GreaterThan.apply)(lhs, rhs)
        case (_, ">=",  Seq(rhs)) => injectCasts(xt.GreaterEquals.apply)(lhs, rhs)
        case (_, "<",   Seq(rhs)) => injectCasts(xt.LessThan.apply)(lhs, rhs)
        case (_, "<=",  Seq(rhs)) => injectCasts(xt.LessEquals.apply)(lhs, rhs)

        case (xt.BVType(_, _), "|",   Seq(rhs)) => injectCasts(xt.BVOr.apply)(lhs, rhs)
        case (xt.BVType(_, _), "&",   Seq(rhs)) => injectCasts(xt.BVAnd.apply)(lhs, rhs)
        case (xt.BVType(_, _), "^",   Seq(rhs)) => injectCasts(xt.BVXor.apply)(lhs, rhs)
        case (xt.BVType(_, _), "<<",  Seq(rhs)) => injectCastsForShift(xt.BVShiftLeft.apply)(lhs, rhs)
        case (xt.BVType(_, _), ">>",  Seq(rhs)) => injectCastsForShift(xt.BVAShiftRight.apply)(lhs, rhs)
        case (xt.BVType(_, _), ">>>", Seq(rhs)) => injectCastsForShift(xt.BVLShiftRight.apply)(lhs, rhs)

        case (xt.BooleanType(), "|", Seq(rhs)) => xt.BoolBitwiseOr(extractTree(lhs), extractTree(rhs))
        case (xt.BooleanType(), "&", Seq(rhs)) => xt.BoolBitwiseAnd(extractTree(lhs), extractTree(rhs))
        case (xt.BooleanType(), "^", Seq(rhs)) => xt.BoolBitwiseXor(extractTree(lhs), extractTree(rhs))

        case (_, "&&",  Seq(rhs)) => xt.And(extractTree(lhs), extractTree(rhs))
        case (_, "||",  Seq(rhs)) => xt.Or(extractTree(lhs), extractTree(rhs))

        case (tpe, "toByte", Seq()) => tpe match {
          case xt.BVType(true, 8) => extractTree(lhs)
          case xt.BVType(true, 16 | 32 | 64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(true, 8))
          case tpe => outOfSubsetError(tr, s"Unexpected cast .toByte from $tpe")
        }

        case (tpe, "toShort", Seq()) => tpe match {
          case xt.BVType(true, 8) => xt.BVWideningCast(extractTree(lhs), xt.BVType(true, 16))
          case xt.BVType(true, 16) => extractTree(lhs)
          case xt.BVType(true, 32 | 64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(true, 16))
          case tpe => outOfSubsetError(tr, s"Unexpected cast .toShort from $tpe")
        }

        case (tpe, "toInt", Seq()) => tpe match {
          case xt.BVType(true, 8 | 16) => xt.BVWideningCast(extractTree(lhs), xt.BVType(true, 32))
          case xt.BVType(true, 32) => extractTree(lhs)
          case xt.BVType(true, 64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(true, 32))
          case tpe => outOfSubsetError(tr, s"Unexpected cast .toInt from $tpe")
        }

        case (tpe, "toLong", Seq()) => tpe match {
          case xt.BVType(true, 8 | 16 | 32 ) => xt.BVWideningCast(extractTree(lhs), xt.BVType(true, 64))
          case xt.BVType(true, 64) => extractTree(lhs)
          case tpe => outOfSubsetError(tr, s"Unexpected cast .toLong from $tpe")
        }

        case (tpe, name, args) =>
          outOfSubsetError(tr,
            s"Unknown call to $name on $lhs of type $tpe (${lhs.tpe}) with " +
              s"arguments ${args mkString ", "} of type " +
              s"${args.map(a => extractType(a)(using dctx.setResolveTypes(true))).mkString(", ")}"
          )
      }
    }
  }

  /** Inject casts for our BitVectors library for methods toByte, toShort, toInt, toLong */
  private def toSigned(e: xt.Expr, signed: Boolean, size1: Int, size2: Int): xt.Expr = {
    // already signed
    if (signed && size1 < size2) xt.BVWideningCast(e, xt.BVType(signed, size2)).copiedFrom(e)
    else if (signed && size1 > size2) xt.BVNarrowingCast(e, xt.BVType(signed, size2)).copiedFrom(e)
    else if (signed) e
    // unsigned
    else if (size1 < size2)
      xt.BVUnsignedToSigned(xt.BVWideningCast(e, xt.BVType(signed, size2)).copiedFrom(e)).copiedFrom(e)
    else if (size1 > size2)
      xt.BVUnsignedToSigned(xt.BVNarrowingCast(e, xt.BVType(signed, size2)).copiedFrom(e)).copiedFrom(e)
    else
      xt.BVUnsignedToSigned(e).copiedFrom(e)
  }

  /** Inject implicit widening casts according to the Java semantics (5.6.2. Binary Numeric Promotion) */
  private def injectCasts(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                         (lhs0: tpd.Tree, rhs0: tpd.Tree)
                         (using dctx: DefContext, cds: ClassDefs): xt.Expr = {
    injectCastsImpl(ctor)(lhs0, rhs0, shift = false)
  }

  /**
   *  Inject casts, special edition for shift operations.
   *
   *  NOTE In THEORY, the rhs needs to be promoted independently of lhs.
   *       In PRACTICE, Inox requires that both operands have the same type.
   *       [[CodeGeneration]] is applying a narrowing cast from Long to Int
   *       if needed. Here we add the opposite, and safe operation when lhs
   *       is a Long. We do not support shift operations when rhs is Long
   *       but lhs is a smaller BVType.
   */
  private def injectCastsForShift(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                                 (lhs0: tpd.Tree, rhs0: tpd.Tree)
                                 (using dctx: DefContext, cds: ClassDefs): xt.Expr = {
    injectCastsImpl(ctor)(lhs0, rhs0, shift = true)
  }

  // TODO: Review
  private def injectCastsImpl(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                             (lhs0: tpd.Tree, rhs0: tpd.Tree, shift: Boolean)
                             (using dctx: DefContext, cds: ClassDefs): xt.Expr = {
    def checkBits(tr: tpd.Tree, tpe: xt.Type) = tpe match {
      case xt.BVType(_, 8 | 16 | 32 | 64) => // Byte, Short, Int or Long are ok
      case xt.BVType(_, s) => outOfSubsetError(tr, s"Unexpected integer of $s bits")
      case _ => // non-bitvector types are ok too
    }

    val lhs = extractTree(lhs0)
    val rhs = extractTree(rhs0)

    val ltpe = extractType(lhs0)(using dctx.setResolveTypes(true))
    checkBits(lhs0, ltpe)
    val rtpe = extractType(rhs0)(using dctx.setResolveTypes(true))
    checkBits(rhs0, rtpe)

    val id = { (e: xt.Expr) => e }
    val widen32 = { (e: xt.Expr) => xt.BVWideningCast(e, xt.BVType(true, 32).copiedFrom(e)).copiedFrom(e) }
    val widen64 = { (e: xt.Expr) => xt.BVWideningCast(e, xt.BVType(true, 64).copiedFrom(e)).copiedFrom(e) }

    val (lctor, rctor) = (ltpe, rtpe) match {
      case (xt.BVType(true, 64), xt.BVType(true, 64))          => (id, id)
      case (xt.BVType(true, 64), xt.BVType(true, _))           => (id, widen64)
      case (xt.BVType(true, _),  xt.BVType(true, 64)) if shift => outOfSubsetError(rhs0, s"Unsupported shift")
      case (xt.BVType(true, _),  xt.BVType(true, 64))          => (widen64, id)
      case (xt.BVType(true, 32), xt.BVType(true, 32))          => (id, id)
      case (xt.BVType(true, 32), xt.BVType(true, _))           => (id, widen32)
      case (xt.BVType(true, _),  xt.BVType(true, 32))          => (widen32, id)
      case (xt.BVType(true, _),  xt.BVType(true, _))           => (widen32, widen32)

      case (xt.BVType(_,_), _) | (_, xt.BVType(_,_)) =>
        outOfSubsetError(lhs0, s"Unexpected combination of types: $ltpe and $rtpe")

      case (_, _) => (id, id)
    }

    ctor(lctor(lhs), rctor(rhs))
  }

  // TODO: Review
  /** Inject implicit widening cast according to the Java semantics (5.6.1. Unary Numeric Promotion) */
  private def injectCast(ctor: xt.Expr => xt.Expr)(e0: tpd.Tree)(using dctx: DefContext, cds: ClassDefs): xt.Expr = {
    val e = extractTree(e0)
    val etpe = extractType(e0)(using dctx.setResolveTypes(true))

    val id = { (e: xt.Expr) => e }
    val widen32 = { (e: xt.Expr) => xt.BVWideningCast(e, xt.Int32Type().copiedFrom(e)).copiedFrom(e) }

    val ector = etpe match {
      case xt.BVType(true, 8 | 16) => widen32
      case xt.BVType(true, 32 | 64) => id
      case xt.BVType(_, s) => outOfSubsetError(e0, s"Unexpected integer type of $s bits")
      case _ => id
    }

    ctor(ector(e))
  }

  // TODO: Recursively traverse type tree
  private def extractTypeTree(tpt: tpd.Tree)(using dctx: DefContext, cds: ClassDefs): Option[xt.Type] = {
    tpt match {
      case ByNameTypeTree(tpe) =>
        val result = xt.FunctionType(Seq(), extractType(tpe, tpe.tpe)).setPos(tpt.sourcePos)
        Some(result)

//      case PredicateTypeTree(vd, pred) =>
//        val subject = xt.ValDef(getIdentifier(vd.symbol), extractType(vd.tpt, vd.tpe)).setPos(vd.pos)
//        val nctx = dctx.withNewVar(vd.symbol -> (() => subject.toVariable))
//        val predExpr = extractTree(pred)(nctx)
//        val result = xt.RefinementType(subject, predExpr).setPos(tpt.pos)
//        Some(result)

      case Select(prefix, name) if !(prefix.symbol.is(ModuleClass) || prefix.symbol.is(Module)) =>
        val path = extractTreeOrNoTree(prefix)
        val id = getIdentifier(tpt.symbol)
        val result = xt.TypeApply(xt.TypeSelect(Some(path).filterNot(_ == xt.NoTree), id), Seq())
        Some(result)

      case _ => None
    }
  }

  // TODO: Review
  private def extractLocalClassType(tr: TypeRef, cid: Identifier, tps: List[xt.Type])
                                   (using dctx: DefContext, pos: SourcePosition, cds: ClassDefs): xt.LocalClassType = {

    val sym = tr.classSymbol
    val tparamsSyms = sym.typeParams.map(_.paramRef.typeSymbol)
    val tparams = extractTypeParams(tparamsSyms)

    val tpCtx = dctx.copy(tparams = dctx.tparams ++ (tparamsSyms zip tparams).toMap)
    val parents = tr.parents.filter(isValidParentType(_)).map(extractType(_)(using tpCtx, pos))

    xt.LocalClassType(cid, tparams.map(xt.TypeParameterDef(_)), tps, parents)
  }

  private def extractType(tpt: tpd.Tree, tpe: Type)(using dctx: DefContext, cds: ClassDefs): xt.Type = {
    // TODO: Why extractTypeTree???
//    extractTypeTree(tpt).getOrElse(stainlessType(tpe)(using dctx, tpt.sourcePos))
    extractType(tpt.tpe)(using dctx, tpt.sourcePos)
  }

  private def extractType(t: tpd.Tree)(using dctx: DefContext, cds: ClassDefs): xt.Type = {
    extractType(t.tpe)(using dctx, t.sourcePos)
  }

  private val etCache = MutableMap[(Type, DefContext), xt.Type]()

  object StrictBVType {
    def unapply(tpe: xt.Type): Option[(Boolean, Int)] = tpe match {
      case xt.AnnotatedType(xt.BVType(signed, size), flags) if flags.contains(xt.StrictBV) =>
        Some((signed , size))
      case _ => None
    }
  }

  // TODO: Review
  // TODO: Do not dealias type members
  private def extractType(tpt: Type)(using dctx: DefContext, pos: SourcePosition, cds: ClassDefs): xt.Type = /*etCache.getOrElseUpdate((tpt -> dctx), */{
    val x = 3123
    val res = (tpt match {
      case NoType => xt.Untyped

      case tpe if tpe.typeSymbol == defn.CharClass    => xt.CharType()
      case tpe if tpe.typeSymbol == defn.ByteClass    => xt.Int8Type()
      case tpe if tpe.typeSymbol == defn.ShortClass   => xt.Int16Type()
      case tpe if tpe.typeSymbol == defn.IntClass     => xt.Int32Type()
      case tpe if tpe.typeSymbol == defn.LongClass    => xt.Int64Type()
      case tpe if tpe.typeSymbol == defn.BooleanClass => xt.BooleanType()
      case tpe if tpe.typeSymbol == defn.UnitClass    => xt.UnitType()
      case tpe if tpe.typeSymbol == defn.NothingClass => xt.NothingType()

      // `isRef` seems to be needed here instead of `==`, as the latter
      // seems to be too lax, and makes the whole test suite fail. - @romac
      case tpe if tpe.isRef(defn.AnyClass) => xt.AnyType()

      case ct: ConstantType => extractType(ct.value.tpe)
      case TypeBounds(lo, hi) =>
        xt.TypeBounds(extractType(lo), extractType(hi), Seq.empty)
      case cet: ExprType => extractType(cet.resultType) // TODO: Should be () => Type ?

      case tpe if isBigIntSym(tpe.typeSymbol) => xt.IntegerType()
      case tpe if isRealSym(tpe.typeSymbol)   => xt.RealType()
      case tpe if isStringSym(tpe.typeSymbol) => xt.StringType()

      case AppliedType(tr: TypeRef, Seq(tp)) if isSetSym(tr.symbol) =>
        xt.SetType(extractType(tp))
/*
      // TODO: Check when this can occur: it seems for class declaration but does not feel right
      case tr: TypeRef if isSetSym(tr.symbol) =>
        val Seq(tp) = extractTypeParams(tr.classSymbol.typeParams)
        xt.SetType(tp)
*/
      case AppliedType(tr: TypeRef, Seq(tp)) if isBagSym(tr.symbol) =>
        xt.BagType(extractType(tp))
/*
      // TODO: Check when this can occur: it seems for class declaration but does not feel right
      case tr: TypeRef if isBagSym(tr.symbol) =>
        val Seq(tp) = extractTypeParams(tr.classSymbol.typeParams)
        xt.BagType(tp)
*/
      case FrontendBVType(signed, size) =>
        xt.AnnotatedType(xt.BVType(signed, size), Seq(xt.StrictBV))

      case AppliedType(tr: TypeRef, tps) if isMapSym(tr.symbol) =>
        val Seq(from, to) = tps map extractType
        xt.MapType(from, xt.ClassType(getIdentifier(optionSymbol), Seq(to)).setPos(pos))
/*
      // TODO: Check when this can occur: it seems for class declaration but does not feel right
      case tr: TypeRef if isMapSym(tr.symbol) =>
        val Seq(from, to) = extractTypeParams(tr.classSymbol.typeParams)
        xt.MapType(from, xt.ClassType(getIdentifier(optionSymbol), Seq(to)).setPos(pos))
*/
      case AppliedType(tr: TypeRef, tps) if isMutableMapSym(tr.symbol) =>
        val Seq(from, to) = tps map extractType
        xt.MutableMapType(from, to)
/*
      // TODO: Check when this can occur: it seems for class declaration but does not feel right
      case tr: TypeRef if isMutableMapSym(tr.symbol) =>
        val Seq(from, to) = extractTypeParams(tr.classSymbol.typeParams)
        xt.MutableMapType(from, to)
*/
      case AppliedType(tr: TypeRef, tps) if TupleSymbol.unapply(tr.classSymbol).isDefined =>
        xt.TupleType(tps map extractType)
/*
      // TODO: Check when this can occur: it seems for class declaration but does not feel right
      case tr: TypeRef if TupleSymbol.unapply(tr.classSymbol).isDefined =>
        xt.TupleType(extractTypeParams(tr.classSymbol.typeParams))
*/
      case AppliedType(tr: TypeRef, Seq(tp)) if isArrayClassSym(tr.symbol) =>
        xt.ArrayType(extractType(tp))
/*
      // TODO: Check when this can occur: it seems for class declaration but does not feel right
      case tr: TypeRef if isArrayClassSym(tr.symbol) =>
        val Seq(tp) = extractTypeParams(tr.classSymbol.typeParams)
        xt.ArrayType(tp)
*/
      // TODO: what is this case doing here???
      /*
      case tp if defn.isFunctionClass(tp.typeSymbol) && tp.dealias.argInfos.isEmpty =>
        xt.FunctionType(Seq(), xt.UnitType())
      */
      case fo @ defn.FunctionOf(from, to, _, _) =>
        xt.FunctionType(from map extractType, extractType(to))

      // TODO: Dans Scalac, check supplémentaire pour symbol isAbstract
      case tr @ TypeRef(_, _) if dctx.tparams contains tr.symbol =>
        dctx.tparams(tr.symbol)
      // TODO: Not doing tt.classSymbol because it gets the "The least class or trait of which this type is a subtype or parameterized"
      case tt @ TypeRef(_, _) if tt.symbol.isClass =>
        val sym = tt.symbol.asClass
        val id = getIdentifier(sym)
        val tparams = sym.typeParams.map { sym =>
          xt.TypeParameter(getIdentifier(sym), Seq())
        }
        dctx.localClasses.get(id) match {
          case Some(lcd) => extractLocalClassType(tt, lcd.id, tparams)
          case None => xt.ClassType(id, tparams)
        }

      // TODO: Seems wrong
      // TODO: Not doing tt.classSymbol because it gets the "The least class or trait of which this type is a subtype or parameterized"
      //  (for instance, a "type Foo = Int => String" gets to enter this case because tt.classSymbol returns Function1, even though we want this type to go through dealiasing and match the function type case)
      case AppliedType(tt @ TypeRef(_, _), args) if tt.symbol.isClass =>
        val sym = tt.symbol.asClass
        val id = getIdentifier(sym)
        dctx.localClasses.get(id) match {
          case Some(lcd) => extractLocalClassType(tt, lcd.id, args map extractType)
          case None => xt.ClassType(id, args map extractType)
        }
      /*
      // TODO: review
      case tr@TypeRef(prefix, _) if tr.symbol.isAbstractOrAliasType || tr.symbol.isOpaqueAlias =>
        val useTypeApply = prefix match {
          case ThisType(nt: NamedType) => nt.symbol.isClass // We do not want to dealias type member within classes, even if they are an alias of another type
          case _ => !dctx.resolveTypes
        }
        if (useTypeApply) {
          val selector = extractPrefix(prefix)
          xt.TypeApply(xt.TypeSelect(selector, getIdentifier(tr.symbol)), Seq.empty)
        } else {
          extractType(tr.widenDealias)(using dctx.setResolveTypes(tr != tr.widenDealias), pos)
        }

      case at@AppliedType(tr@TypeRef(prefix, _), args) if tr.symbol.isAbstractOrAliasType || tr.symbol.isOpaqueAlias =>
        val useTypeApply = prefix match {
          case ThisType(nt: NamedType) => nt.symbol.isClass
          case _ => !dctx.resolveTypes
        }
        if (useTypeApply) {
          val selector = extractPrefix(prefix)
          xt.TypeApply(xt.TypeSelect(selector, getIdentifier(tr.symbol)), args map extractType)
        } else {
          extractType(at.derivedAppliedType(tr.widenDealias, args))(using dctx.setResolveTypes(tr != tr.widenDealias), pos)
        }
      */

      case tr: TypeRef if dctx.resolveTypes && tr.symbol.isAbstractOrAliasType =>
        // TODO: is widening desired?
        extractType(tr.widenDealias)(using dctx.setResolveTypes(tr != tr.widenDealias), pos)

      // TODO: Is this ok?
      case tr @ TypeRef(prefix, _) if tr.symbol.isAbstractOrAliasType || tr.symbol.isOpaqueAlias =>
        val selector = extractPrefix(prefix)
        xt.TypeApply(xt.TypeSelect(selector, getIdentifier(tr.symbol)), Seq.empty)

      // TODO: This "dctx.resolvesTypes & dealias" should be checked more often!!!
      // TODO: so that e.g. Env[K] defined as type Env[A] = A => String passes through dealiasing
      // TODO: Is this ok?
      case at@AppliedType(tr @ TypeRef(prefix, _), args) if dctx.resolveTypes && tr.symbol.isAbstractOrAliasType =>
        // TODO: is widening desired?
        extractType(at.derivedAppliedType(tr.widenDealias, args))(using dctx.setResolveTypes(tr != tr.widenDealias), pos)

      // TODO: Is this ok?
      case AppliedType(tr @ TypeRef(prefix, _), args) if tr.symbol.isAbstractOrAliasType || tr.symbol.isOpaqueAlias =>
        val selector = extractPrefix(prefix)
        xt.TypeApply(xt.TypeSelect(selector, getIdentifier(tr.symbol)), args map extractType)


      /*
      // superseded by extractPrefix thing
      case tr @ TypeRef(ref: TermRef, name) if !dctx.resolveTypes && (tr.symbol.isAbstractOrAliasType || tr.symbol.isOpaqueAlias) =>
        val path = if ((ref.symbol is Module) || (ref.symbol is ModuleClass)) {
          None
        } else {
          val id = SymbolIdentifier(ref.name.mangledString)
          val vd = xt.ValDef(id, extractType(ref.underlying), Seq.empty).setPos(pos)
          Some(vd.toVariable)
        }

        val selector = getIdentifier(tr.symbol)
        xt.TypeApply(xt.TypeSelect(path, selector).setPos(pos), Seq.empty)
      */
      /*
      // superseded by extractPrefix thing
      case tr @ TypeRef(thisRef: ThisType, _) if tr.symbol.isAbstractOrAliasType || tr.symbol.isOpaqueAlias =>
        val thiss =
          if (thisRef.tref.symbol is ModuleClass)
            None
          else
            extractType(thisRef) match {
              case ct: xt.ClassType => Some(xt.This(ct).setPos(pos))
              case lct: xt.LocalClassType => Some(xt.LocalThis(lct).setPos(pos))
            }

        val selector = getIdentifier(tr.symbol)
        xt.TypeApply(xt.TypeSelect(thiss, selector).setPos(pos), Seq.empty).setPos(pos)
      */
      /*
      case tt @ ThisType(tr) =>
        extractType(tr)
      */
      // TODO: Ok?
      case tt: ThisType =>
        val id = getIdentifier(tt.tref.symbol)
        val params = tt.tref.symbol.typeParams.map(dctx.tparams)
        dctx.localClasses.get(id) match {
          case Some(lcd) => extractLocalClassType(tt.tref, lcd.id, params)
          case None => xt.ClassType(id, params)
        }

      case st @ SuperType(thisTpe, superTpe) =>
        extractType(superTpe)

      // TODO: Things about "SingleType" with sym.isModule and sym.isTerm

      /////////////

      case tr @ TypeRef(ref: TermParamRef, _) if dctx.depParams contains ref.paramName =>
        val vd = dctx.depParams(ref.paramName).setPos(pos)
        val selector = getIdentifier(tr.symbol)
        xt.TypeApply(xt.TypeSelect(Some(vd.toVariable), selector).setPos(pos), Seq.empty)

      // TODO: ???

      case tr: TypeRef if tr.symbol.isOpaqueAlias && dctx.resolveTypes =>
        extractType(tr.translucentSuperType)

      case tt @ TypeRef(prefix: TermRef, name) if prefix.underlying.classSymbol.typeParams.exists(_.name == name) =>
        extractType(TypeRef(prefix.widenTermRefExpr, name))

      case tt @ TypeRef(prefix, name) if prefix.classSymbol.typeParams.exists(_.name == name) =>
        val idx = prefix.classSymbol.typeParams.indexWhere(_.name == name)
        (extractType(prefix), idx) match {
          case (xt.MapType(from, ct @ xt.ClassType(id, Seq(to))), 1) => to
          case (tp @ xt.NAryType(tps, _), _) => tps(idx)
        }

      ///////////////

      // Dependent function type
      case tp: RefinedType if defn.isFunctionType(tp) =>
        val mt = tp.refinedInfo.asInstanceOf[MethodType]

        val vds = (mt.paramNames zip mt.paramInfos) map { case (name, tpe) =>
          xt.ValDef(SymbolIdentifier(name.mangledString), extractType(tpe), Seq.empty)
        }

        val rctx = dctx.withDepParams(mt.paramNames zip vds)
        val resultType = extractType(mt.resultType)(using rctx, pos)

        xt.PiType(vds, resultType)

      // TODO: ???
      case RefinedType(p, name, tpe) =>
        val idx = p.classSymbol.typeParams.indexWhere(_.name == name)
        (extractType(p), idx) match {
          case (xt.MapType(from, ct @ xt.ClassType(id, Seq(to))), 1) =>
            xt.MapType(from, xt.ClassType(id, Seq(extractType(tpe))).copiedFrom(ct))
          case (xt.NAryType(tps, recons), _) =>
            recons(tps.updated(idx, extractType(tpe)))
        }

      // TODO: ???
      case at @ AppliedType(tr: TypeRef, args) if tr.symbol.info.isTypeAlias && dctx.resolveTypes =>
        extractType(at.widenDealias)

      // TODO: ???
      case at @ AppliedType(tr: TypeRef, args) if tr.symbol.info.isTypeAlias =>
        xt.TypeApply(xt.TypeSelect(None, getIdentifier(tr.symbol)), args map extractType)

      /*
      // superseded
      case at @ AppliedType(tycon: TypeRef, args) =>
        val sym = at.classSymbol
        val id = getIdentifier(sym)
        val tps = args map extractType
        dctx.localClasses.get(id) match {
          case Some(lcd) => extractLocalClassType(tycon, lcd.id, tps)
          case None => xt.ClassType(id, tps)
        }
      */

      // TODO: ???
      case tt @ TermRef(_, _) if dctx.resolveTypes =>
        extractType(tt.widenDealias)

      // TODO: ???
      case tt @ TermRef(_, _) =>
        extractType(tt.widenTermRefExpr)

      case AndType(tp, prod) if prod.typeSymbol == defn.ProductClass => extractType(tp)
      case AndType(prod, tp) if prod.typeSymbol == defn.ProductClass => extractType(tp)
      case AndType(tp, prod) if defn.isProductClass(prod.typeSymbol) => extractType(tp)
      case AndType(prod, tp) if defn.isProductClass(prod.typeSymbol) => extractType(tp)
      case AndType(tp, ser) if ser.typeSymbol == defn.SerializableClass => extractType(tp)
      case AndType(ser, tp) if ser.typeSymbol == defn.SerializableClass => extractType(tp)

      case ot: OrType => extractType(ot.join)

      case pp @ TypeParamRef(binder, num) =>
        dctx.typeParamRefs.getOrElse(pp,
          dctx.tparams.collect { case (k, v) if k.name == pp.paramName => v }.lastOption.getOrElse {
            outOfSubsetError(tpt.typeSymbol.sourcePos, s"Stainless does not support type $tpt in context ${dctx.tparams}")
          })

      case tp: TypeVar => extractType(tp.stripTypeVar)

      case AnnotatedType(tpe, ExIndexedAt(n)) =>
        xt.AnnotatedType(extractType(tpe), Seq(xt.IndexedAt(extractTree(n))))

      case AnnotatedType(tpe, _) => extractType(tpe)

      // TODO: Check if we still need this
//        def keysOf(value: B): List[A] = {
//          toList.filter(_._2 == value).map(_._1)
//        }
      case TypeRef(SkolemType(AppliedType(tr: TypeRef, List(arg1, arg2))), desig)
        if tr.symbol == defn.TypeBoxClass && desig == defn.TypeBox_CAP && arg1 == arg2 =>
        extractType(arg1)

      case _ =>
        if (tpt ne null) {
          outOfSubsetError(tpt.typeSymbol.sourcePos, s"Stainless does not support type $tpt")
        } else {
          outOfSubsetError(NoSourcePosition, "Tree with null-pointer as type found")
        }
    }).setPos(pos)

    res
  } // )

  private def extractPrefix(prefix: Type)(using dctx: DefContext, pos: SourcePosition, cds: ClassDefs): Option[xt.Expr] = {
    // TODO: Sort this out
    val sym = prefix match {
      case t: TermRef => t.symbol
      case t: ThisType => t.tref.symbol
      case _ => NoSymbol
    }
    prefix match {
      // TODO: Scalac does not check checks against module
      case _ if (sym is Module) || (sym is ModuleClass) =>
        None
      case thiss: ThisType =>
        val id = getIdentifier(sym)
        // TODO: orig does a extractType (mmh, seems more or less the same)
        dctx.localClasses.get(id) match {
          case Some(lcd) => Some(xt.LocalThis(extractType(thiss).asInstanceOf[xt.LocalClassType]))
          case None => Some(xt.This(extractType(thiss).asInstanceOf[xt.ClassType]))
        }
      case _: SingletonType =>
        Some(dctx.vars.getOrElse(sym,
          outOfSubsetError(NoSourcePosition, s"extractPrefix: could not find variable $sym in context"))())
      case _ => None
    }
  }
}
