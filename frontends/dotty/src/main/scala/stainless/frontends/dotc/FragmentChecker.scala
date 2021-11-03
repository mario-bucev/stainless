package stainless
package frontends.dotc

import dotty.tools.dotc.*
import core.*
import Symbols.*
import Contexts.Context as DottyContext
import ast.Trees
import Types.*
import Trees.*
import ast.tpd
import Flags.*
import Annotations.*
import StdNames.*
import Names.*
import util.SourcePosition

import scala.collection.mutable

/**
 * This class contains a traverser that rejects Scala programs that don't fit in the
 * PureScala or ImperativeScala fragments.
 *
 * Some interesting cases:
 *
 *  - pattern match variables are fresh variables that have to "inherit" the @ghost annotation
 *    from the corresponding case class field
 *  - case classes generate a large number of synthetic methods that need to be patched with @ghost
 *    in cases where there are @ghost parameters
 *  - some case class synthetics will contain invalid accesses to ghost code (i.e. methods equals and unapply)
 *    but we don't report the errors in synthetic code. This is harmless and the ghost code will be
 *    removed as usual
 *
 * This class mutates some symbols by adding the @ghost annotation (see cases above). The AST is not changed.
 */
class FragmentChecker(inoxCtx: inox.Context)(using override val dottyCtx: DottyContext) extends ASTExtractors {

  import ExpressionExtractors._
  import StructuralExtractors._

  private val erroneousPositions = mutable.Set.empty[Int]

  /**
   * Report an error, unless there is already an error reported at the same position.
   */
  private def reportError(pos: SourcePosition, msg: String): Unit = {
    if (!erroneousPositions(pos.start)) {
      inoxCtx.reporter.error(pos, msg)
      erroneousPositions += pos.start
    }
  }

  def hasErrors(): Boolean = erroneousPositions.nonEmpty

  def ghostChecker(tree: tpd.Tree): Unit = (new GhostAnnotationChecker)((), tree)

  def checker(tree: tpd.Tree): Unit = (new Checker)((), tree)


  class GhostAnnotationChecker extends tpd.TreeTraverser {
    val ghostAnnotation = Symbols.requiredClass("stainless.annotation.ghost")
    val ghostMethod = Symbols.requiredPackage("stainless.lang").denot.info.member(Names.termName("ghost"))

    private var ghostContext: Boolean = false

    def withinGhostContext[A](body: => A): A = {
      val old = ghostContext
      ghostContext = true
      val res = body
      ghostContext = old
      res
    }

    // Note: we not have a isGhostDefaultGetter because Dotty does not generate getters for fields

    /**
     * Methods that should be considered as part of a ghost context, even though they are not
     * explicitly ghost. They are typically synthetic methods for case classes that are harmless
     * if they touch ghost code
     */
    private def effectivelyGhost(sym: Symbol): Boolean = {
      // copy$default$n are synthetic methods that simply return the n-th (starting from 1) constructor field
      def isCopyDefault = sym.name match {
        case DerivedName(nme.copy, kind) =>
          sym.name is NameKinds.DefaultGetterName
        case _ => false
      }
      def isProductAccessor = sym.name match {
        case nme._1 | nme._2 | nme._3 | nme._4 | nme._5 | nme._6 | nme._7 | nme._8 | nme._9 | nme._10 |
             nme._11 | nme._12 | nme._13 | nme._14 | nme._15 | nme._16 | nme._17 | nme._18 | nme._19 | nme._20 |
             nme._21 | nme._22 => true
        case _ => false
      }

      (sym is Synthetic) &&
      (
        (
          (sym.owner is CaseClass) &&
          (
            sym.name == nme.equals_ ||
            sym.name == nme.productElement ||
            sym.name == nme.hashCode_ ||
            isCopyDefault ||
            isProductAccessor
          )
        ) ||
        (
          (sym.owner.companionClass is CaseClass) &&
          sym.name == nme.unapply
        )
      )
    }

    private def symbolIndex(tree: tpd.Tree): Int = tree match {
      case Apply(fun, args) => symbolIndex(fun) + 1
      case _ => 0
    }

    def isCaseCopy(s: Symbol): Boolean =
      // isMethod && owner.isCase && isSynthetic && name == nme.copy
      (s is Method) && (s.owner is Case) && (s is Synthetic) && s.name == nme.copy

    def isCaseApply(s: Symbol): Boolean =
      // The apply method is to be found in the module class, so we need to check that its owner is indeed a ModuleClass
      (s is Method) && (s.owner is ModuleClass) && (s is Synthetic) && s.name == nme.apply && (s.owner.companionClass.exists)

    /**
     * Synthetics introduced by typer for case classes won't propagate the @ghost annotation
     * to the copy method or for default arguments, leading to invalid accesses from non-ghost
     * code to ghost code. We fix it here by adding @ghost to these synthetics
     */
    private def propagateGhostAnnotation(m: tpd.MemberDef): Unit = {
      val sym = m.symbol
      lazy val isCopy = isCaseCopy(sym)
      lazy val isApply = isCaseApply(sym)
      // TODO: What is this thing???
      if (sym is Artifact) m match {
        // TODO: Extract on rhs: is it ok?
        // TODO: Can't be tested at runtime
        case vd @ ValDef(_, _, ExCall(_, c, _, _)) if /*isDefaultGetter(c) && */ c.hasAnnotation(ghostAnnotation) =>
          sym.addAnnotation(ghostAnnotation)
        case _ => ()
      }
      else if (isCopy || isApply) {
        // TODO: ensure this is correct. TODO: caseClassParams: we want fields, not params
        val fields =
          if (isCopy) sym.owner.denot.asClass.classInfo.fields
          // The apply method is in the module class; we get the actual case class using companionClass
          else sym.owner.companionClass.denot.asClass.classInfo.fields
        val ctorFields = fields.map(_.symbol).filter(fld => (fld is CaseAccessor) || (fld is ParamAccessor))
        val params = m.asInstanceOf[tpd.DefDef].termParamss.flatten.map(_.symbol)
        for ((ctorField, param) <- ctorFields.zip(params) if ctorField.hasAnnotation(ghostAnnotation))
          param.addAnnotation(ghostAnnotation)
        /*
        // orig
        val caseClassParams = sym.owner.primaryConstructor.info.params
        for ((copyParam, caseParam) <- sym.info.params.zip(caseClassParams) if caseParam.hasAnnotation(ghostAnnotation))
          copyParam.addAnnotation(ghostAnnotation)
        */
      }
      /*else if (sym.isDefaultGetter && isGhostDefaultGetter(m)) {
        sym.addAnnotation(ghostAnnotation)
      }*/
      else if (sym.isSetter && sym.hasAnnotation(ghostAnnotation)) {
        // make the setter parameter ghost but the setter itself stays non-ghost. this allows it
        // to be called from non-ghost code and at the same time allows assigning ghost state via the ghost argument
        sym.removeAnnotation(ghostAnnotation)
        val param = m.asInstanceOf[tpd.DefDef].termParamss.flatten.head // TODO: but we annotate that only if the setter is explicitly set to have ghostAnnotation?
        param.symbol.addAnnotation(ghostAnnotation)
      }
      // TODO: verify this thing
      else if (((sym is Module) || (sym is ModuleClass)) && sym.companionClass.hasAnnotation(ghostAnnotation)) {
        sym.addAnnotation(ghostAnnotation)
        sym.moduleClass.addAnnotation(ghostAnnotation)
      }
    }

    override def traverse(tree: tpd.Tree)(using ctx: DottyContext): Unit = {
      val sym = tree.symbol
      val x = 3
      tree match {
        case Ident(_) if sym.hasAnnotation(ghostAnnotation) && !ghostContext =>
          reportError(tree.sourcePos, s"Cannot access a ghost symbol outside of a ghost context. [ $tree in ${ctx.owner} ]")

        case Select(qual, _) if sym.hasAnnotation(ghostAnnotation) && !ghostContext =>
          reportError(tree.sourcePos, s"Cannot access a ghost symbol outside of a ghost context. [ $tree in ${ctx.owner} ]")
          traverseChildren(tree)

        case m: tpd.MemberDef  =>
          // TODO: Accessor: verify what happens for setters
          if ((m.symbol is Synthetic) || (m.symbol is Accessor) || (m.symbol is Artifact))
            propagateGhostAnnotation(m)

          // We consider some synthetic methods values as being inside ghost
          // but don't auto-annotate as such because we don't want all code to be removed.
          // They are synthetic case class methods that are harmless if they see some ghost nulls
          if (m.symbol.hasAnnotation(ghostAnnotation) || effectivelyGhost(sym))
            withinGhostContext(traverseChildren(m))
          else
            traverseChildren(m)

        case f @ Apply(fun, args) if fun.symbol.hasAnnotation(ghostAnnotation) =>
          traverse(fun)
          withinGhostContext(args foreach traverse)

        case UnApply(fun, _, args) if fun.symbol.name == nme.unapply && (fun.symbol is Synthetic) =>
          traverse(fun)

          // The pattern match variables need to add the ghost annotation from their case class ctor fields
          // We only do that for case classes synthesized unapply methods.

          val caseClassSym = fun.symbol.denot.owner // The owner of the unapply method is the companion object
            .denot.companionClass.asClass // We need the class itself to get the case class ctor fields
          val ctorFields = caseClassSym.classInfo.fields.map(_.symbol).filter(fld => (fld is CaseAccessor) || (fld is ParamAccessor))
          for ((param, arg) <- ctorFields.zip(args))
            if (param.hasAnnotation(ghostAnnotation)) {
              arg match {
                case b@Bind(_, body) =>
                  b.symbol.addAnnotation(ghostAnnotation)
                  traverse(body)
                case _ =>
                  traverse(arg)
              }
            } else
              traverse(arg)

        case f @ Apply(fun, args) =>
          traverse(fun)

          val params = fun.symbol.denot.paramSymss
          val leadingTypeParams = params.exists(_.exists(_.isType))
          val termParams = if (leadingTypeParams) params.tail else params

          for ((param, arg) <- termParams(symbolIndex(fun)).zip(args))
            if (param.hasAnnotation(ghostAnnotation))
              withinGhostContext(traverse(arg))
            else
              traverse(arg)

        case Assign(lhs, rhs) =>
          if (lhs.symbol.hasAnnotation(ghostAnnotation))
            withinGhostContext(traverse(rhs))
          else
            traverseChildren(tree)

        case _ =>
          traverseChildren(tree)
      }
    }
  }

  class Checker extends tpd.TreeTraverser {
    val StainlessLangPackage = Symbols.requiredPackage("stainless.lang")
    val ExternAnnotation = Symbols.requiredClass("stainless.annotation.extern")
    val IgnoreAnnotation = Symbols.requiredClass("stainless.annotation.ignore")
    val StainlessOld = StainlessLangPackage.info.decl(Names.termName("old")).symbol

    val BigInt_ApplyMethods =
      (StainlessLangPackage.info.decl(Names.termName("BigInt")).info.decl(nme.apply).alternatives
      ++ Symbols.requiredModule("scala.math.BigInt").info.decl(nme.apply).alternatives).toSet

    val RequireMethods =
      (defn.ScalaPredefModule.info.decl(Names.termName("require")).alternatives.toSet
        + Symbols.requiredModule("stainless.lang.StaticChecks").info.decl(Names.termName("require")))

    private val stainlessReplacement = mutable.Map(
      defn.ListClass -> "stainless.collection.List",
      defn.NilModule.moduleClass -> "stainless.collection.Nil",
      defn.OptionClass -> "stainless.lang.Option",
      Symbols.requiredClass("scala.util.Either") -> "stainless.lang.Either",
      defn.ScalaPackageClass.info.decl(Names.termName("Nil")) -> "stainless.collection.Nil",
      Symbols.requiredClass("scala.collection.immutable.Map") -> "stainless.lang.Map",
      Symbols.requiredClass("scala.collection.immutable.Set") -> "stainless.lang.Set"
    )

    // method println is overloaded, so we need to add all overloads to our map
    addOverloadsToMap(defn.ScalaPredefModule.info.decl(Names.termName("println")).symbol, "stainless.io.StdOut.println")

    private def addOverloadsToMap(sym: Symbol, replacement: String): Unit =
      sym.alternatives.foreach(a => stainlessReplacement += a -> replacement)

    // TODO: Test this
    private def checkType(pos: SourcePosition, tpe: Type): Unit = {
      val tyAcc = new TypeAccumulator[Set[(Type, String)]] {
        override def apply(acc: Set[(Type, String)], tp: Type): Set[(Type, String)] = {
          val repl =
            if (stainlessReplacement.contains(tp.dealias.typeSymbol))
              Set(tp -> stainlessReplacement(tp.typeSymbol))
            else Set.empty
          foldOver(acc ++ repl, tp)
        }
      }

      for ((tp, replacement) <- tyAcc(Set.empty, tpe)) {
        reportError(pos, s"Scala API `$tp` is not directly supported, please use `$replacement` instead.")
      }
    }

    private var classBody = false
    def inClassBody[T](f: => T): T = {
      val old = classBody
      classBody = true
      val res = f
      classBody = old
      res
    }

    // TODO: atOwner things removed
    override def traverse(tree: tpd.Tree)(using ctx: DottyContext): Unit = {
      val sym = tree.symbol
      if (sym.exists) {
        val isExtern = sym.hasAnnotation(ExternAnnotation)
        val isIgnore = sym.hasAnnotation(IgnoreAnnotation)

        // exit early if it's a subtree we shouldn't validate
        if (isExtern || isIgnore || (sym is Synthetic)) {
          return ()
        }

        // ignore param & case accessors because they are duplicates of constructor parameters.
        // We catch them when we check constructors
        if (!((sym is ParamAccessor) || (sym is CaseAccessor))) {
          checkType(tree.sourcePos, tree.tpe)
        }
      } else {
        traverseChildren(tree)
        return () // TODO: Not in original
      }

      tree match {
        case od @ ExObjectDef() =>
          val template = od.rhs.asInstanceOf[tpd.Template]
          if (template.parents.exists(p => !isIgnored(p.tpe))) {
            reportError(tree.sourcePos, "Objects cannot extend classes or implement traits, use a case object instead")
          }
          traverseChildren(od)

        case cd @ ExClassDef() =>
          // TODO: mmmh, a bit lackluster?
          val isSupported =
            sym.isClass ||
            (sym is Implicit) ||
            sym.isAnnotation

          if (!isSupported) {
            reportError(tree.sourcePos, "Only abstract classes, case classes, anonymous classes, and objects are allowed in Stainless.")
          }

          val template = cd.rhs.asInstanceOf[tpd.Template]
          val parents = template.parents.map(_.tpe).filterNot(isIgnored)
          if (parents.length > 1) {
            reportError(tree.sourcePos, s"Stainless supports only simple type hierarchies: Classes can only inherit from a single class/trait")
          }

          template.body.foreach {
            case nested @ ExClassDef() =>
              reportError(nested.sourcePos, "Classes can only be defined at the top-level, within objects, or within methods")
            case tr => traverse(tr)
          }

        case dd @ DefDef(_, _, _, _) if sym.isConstructor =>
          /*
          // TODO: what is this?
          if (dd.termParamss.flatten.exists(p => !sym.owner.info.member(p.name).isAccessor))
            reportError(tree.sourcePos, "Non-field constructor parameters are not allowed in Stainless.")
          */
          if (dd.termParamss.size > 1)
            reportError(tree.sourcePos, "Multi-clauses classes are not allowed in Stainless.")
          if (!dd.termParamss.flatten.isEmpty && (sym.owner isOneOf AbstractOrTrait))
            reportError(tree.sourcePos, "Abstract class and trait constructor parameters are not allowed in Stainless.")
          traverse(dd.rhs)

        case dd @ DefDef(_, _, _, _) =>
          // recur only inside `dd.rhs`, as parameter/type parameters have been checked already in `checkType`
          traverse(dd.rhs)

        case vd @ ValDef(_, _, _) if sym.owner.isClass && !(sym.owner isOneOf AbstractOrTrait) && (sym is Mutable) && !(sym is CaseAccessor) && !(sym is ParamAccessor) => // TODO: ParamAccessor added
          reportError(tree.sourcePos, "Variables are only allowed within functions and as constructor parameters in Stainless.")

        case Apply(fun, List(arg)) if sym == StainlessOld =>
          arg match {
            case This(_) => ()
            case t if t.symbol.isTerm && (t.symbol is Mutable) && !(t.symbol is Method) => () // TODO: enough for isVariable?
            case t =>
              reportError(t.sourcePos, s"Stainless `old` is only defined on `this` and variables.")
          }

        case Apply(fun, args) if BigInt_ApplyMethods(sym) =>
          if (args.size != 1 || !args.head.isInstanceOf[tpd.Literal])
            reportError(args.head.sourcePos, "Only literal arguments are allowed for BigInt.")

        case ExCall(Some(s @ Select(Super(_, _), _)), _, _, _) =>
          if ((s.symbol is Abstract) && !s.symbol.isConstructor)
            reportError(tree.sourcePos, "Cannot issue a super call to an abstract method.")

        case Apply(fun, args) =>
          if (stainlessReplacement.contains(sym))
            reportError(tree.sourcePos, s"Scala API ($sym) no longer extracted, please use ${stainlessReplacement(sym)}")

        case tpl @ Template(parents, _, self, _) =>
          for (t <- tpl.body if !(t.isDef || t.isType || t.isEmpty || t.isInstanceOf[tpd.Import])) {
            // `require` is allowed inside classes, but not inside objects
            if (RequireMethods(t.symbol) && (ctx.owner is ModuleClass))
              reportError(t.sourcePos, "`require` is not allowed inside object bodies.")
            else
              reportError(t.sourcePos, "Only definitions are allowed inside class bodies.")
          }

          traverseChildren(tree)

        case _ =>
          traverseChildren(tree)
      }
    }
  }
}