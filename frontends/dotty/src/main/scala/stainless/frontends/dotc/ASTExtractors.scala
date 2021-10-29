package stainless
package frontends.dotc

import scala.language.implicitConversions
import dotty.tools.dotc.*
import typer.Inliner
import ast.tpd
import ast.Trees.*
import core.Contexts.{NoContext, Context as DottyContext}
import core.NameKinds
import core.Constants.*
import core.Names.*
import core.NameOps.*
import core.StdNames.*
import core.Symbols.*
import core.Types.*
import core.Flags.*
import core.Annotations.*
import common.ClassDefs

import scala.collection.mutable.Map as MutableMap

trait ASTExtractors {
  val dottyCtx: DottyContext
  import dottyCtx.given

  def classFromName(nameStr: String): ClassSymbol = requiredClass(typeName(nameStr))
  def moduleFromName(nameStr: String): TermSymbol = requiredModule(typeName(nameStr))

  def getAnnotations(sym: Symbol, ignoreOwner: Boolean = false): Seq[(String, Seq[tpd.Tree])] = {
    if (sym eq NoSymbol)
      return Seq.empty

    val erased = if (sym.isEffectivelyErased) Seq(("ghost", Seq.empty[tpd.Tree])) else Seq()
    val selfs = sym.annotations
    val owners =
      if (ignoreOwner) List.empty[Annotation]
      else sym.owner.annotations.filter(annot =>
        annot.toString != "stainless.annotation.export" &&
          !annot.toString.startsWith("stainless.annotation.cCode.global")
      )
    val companions = List(sym.denot.companionModule).filter(_ ne NoSymbol).flatMap(_.annotations)
    erased ++ (for {
      a <- selfs ++ owners ++ companions
      name = a.symbol.showFullName
        .replace(".package.", ".")
    } yield {
      if (name startsWith "stainless.annotation.") {
        val shortName = name drop "stainless.annotation.".length
        Some(shortName, a.arguments)
      } else if (name == "inline" || name == "scala.inline") {
        Some("inline", a.arguments)
      } else {
        None
      }
    }).flatten.foldLeft[(Set[String], Seq[(String, Seq[tpd.Tree])])]((Set(), Seq())) {
      case (acc @ (keys, _), (key, _)) if keys contains key => acc
      case ((keys, seq), (key, args)) => (keys + key, seq :+ (key -> args))
    }._2
  }

  // Well-known symbols that we match on

  protected lazy val scalaAnySym  = classFromName("scala.Any")
  protected lazy val scalaMapSym  = classFromName("scala.collection.immutable.Map")
  protected lazy val scalaSetSym  = classFromName("scala.collection.immutable.Set")
  protected lazy val scalaListSym = classFromName("scala.collection.immutable.List")

  protected lazy val scalaProductClassSym = classFromName("scala.Product")

  protected lazy val exceptionSym = classFromName("stainless.lang.Exception")

  protected lazy val setSym         = classFromName("stainless.lang.Set")
  protected lazy val mapSym         = classFromName("stainless.lang.Map")
  protected lazy val mutableMapSym  = classFromName("stainless.lang.MutableMap")
  protected lazy val bagSym         = classFromName("stainless.lang.Bag")
  protected lazy val realSym        = classFromName("stainless.lang.Real")

  protected lazy val bvSym          = classFromName("stainless.math.BitVectors.BV")

  protected lazy val optionSymbol = classFromName("stainless.lang.Option")
  protected lazy val someSymbol   = classFromName("stainless.lang.Some")
  protected lazy val noneSymbol   = classFromName("stainless.lang.None")

  protected lazy val listSymbol = classFromName("stainless.collection.List")
  protected lazy val consSymbol = classFromName("stainless.collection.Cons")
  protected lazy val nilSymbol  = classFromName("stainless.collection.Nil")

  protected lazy val optionClassSym     = classFromName("scala.Option")
  protected lazy val arraySym           = classFromName("scala.Array")
  protected lazy val someClassSym       = classFromName("scala.Some")
  protected lazy val bigIntSym          = classFromName("scala.math.BigInt")
  protected lazy val stringSym          = classFromName("java.lang.String")

  protected def functionTraitSym(i:Int) = {
    require(0 <= i && i <= 22)
    classFromName("scala.Function" + i)
  }

  def isTuple(sym: Symbol, size: Int): Boolean = {
    (size > 0 && size <= 22) && {
      (sym == classFromName(s"scala.Tuple$size")) ||
      (sym == moduleFromName(s"scala.Tuple$size"))
    }
  }

  object TupleSymbol {
    // It is particularly time expensive so we cache this.
    private val cache = MutableMap[Symbol, Option[Int]]()
    private val cardinality = """Tuple(\d{1,2})""".r
    def unapply(sym: Symbol): Option[Int] = cache.getOrElse(sym, {
      // First, extract a guess about the cardinality of the Tuple.
      // Then, confirm that this is indeed a regular Tuple.
      val name = sym.originalName.toString
      val res = name match {
        case cardinality(i) if isTuple(sym, i.toInt) => Some(i.toInt)
        case _ => None
      }

      cache(sym) = res
      res
    })

    def unapply(tpe: Type): Option[Int] = tpe.classSymbols.collectFirst { case TupleSymbol(i) => i }

    def unapply(tree: tpd.Tree): Option[Int] = unapply(tree.tpe)
  }

  def isBigIntSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) == bigIntSym

  def isStringSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) match { case `stringSym` => true case _ => false }

//  def isByNameSym(sym : Symbol) : Boolean = getResolvedTypeSym(sym) == byNameSym

  // Resolve type aliases
  def getResolvedTypeSym(sym: Symbol): Symbol = {
    if (sym.isAliasType) {
      getResolvedTypeSym(sym.info.resultType.typeSymbol)
    } else {
      sym
    }
  }

  def isBVSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == bvSym
  }

  def isAnySym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaAnySym
  }

  def isSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == setSym
  }

  def isMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == mapSym
  }

  def isMutableMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == mutableMapSym
  }

  def isBagSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == bagSym
  }

  def isRealSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == realSym
  }

  def isScalaSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaSetSym
  }

  def isScalaListSym(sym: Symbol): Boolean = {
    getResolvedTypeSym(sym) == scalaListSym
  }

  def isScalaMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaMapSym
  }

  def isOptionClassSym(sym : Symbol) : Boolean = {
    sym == optionClassSym || sym == someClassSym
  }

  def isFunction(sym: Symbol, i: Int) : Boolean = {
    0 <= i && i <= 22 && sym == functionTraitSym(i)
  }

  def isArrayClassSym(sym: Symbol): Boolean = sym == arraySym

  def hasIntType(t: tpd.Tree) = {
    // val tpe = t.tpe.widen
    t.tpe frozen_<:< defn.IntClass.info
  }

  def hasBigIntType(t: tpd.Tree) = isBigIntSym(t.tpe.typeSymbol)

  def hasStringType(t: tpd.Tree) = isStringSym(t.tpe.typeSymbol)

  // TODO: Verify these
  private lazy val bvtypes = Set(defn.ByteType, defn.ShortType, defn.IntType, defn.LongType)

  def hasBVType(t: tpd.Tree) = bvtypes.exists(bv => t.tpe/*.widen*/ frozen_<:< bv)

  def hasNumericType(t: tpd.Tree): Boolean = hasBigIntType(t) || hasBVType(t) || hasRealType(t)

  def hasRealType(t: tpd.Tree) = isRealSym(t.tpe.typeSymbol)

  def hasBooleanType(t: tpd.Tree) = t.tpe/*.widen*/ frozen_<:< defn.BooleanType

  def isDefaultGetter(sym: Symbol) = {
    (sym is Synthetic) && sym.name.isTermName && sym.name.toTermName.toString.contains("$default$")
  }

  def isCopyMethod(sym: Symbol) = {
    (sym is Synthetic) && sym.name.isTermName && sym.name.toTermName.toString.startsWith("copy")
  }

  def canExtractSynthetic(sym: Symbol) = {
    (sym is Implicit) ||
    isDefaultGetter(sym) ||
    isCopyMethod(sym)
  }

  import AuxiliaryExtractors._
  import ExpressionExtractors._
  import StructuralExtractors._

  // Actual extractors

  object AuxiliaryExtractors {
    object ExSelected {
      def unapplySeq(select: tpd.Select): Option[Seq[String]] = select match {
        case Select(This(tname), name) =>
          Some(Seq(tname.toString, name.toString))
        case Select(from: tpd.Select, name) =>
          unapplySeq(from).map(seq => seq :+ name.toString)
        case Select(from: tpd.Ident, name) =>
          Some(Seq(from.toString, name.toString))
        case _ => None
      }
    }

    object ExNamed {
      def unapply(name: Name): Option[String] = Some(name.toString)
    }

    object ExSymbol {
      def unapplySeq(arg: Any): Option[Seq[String]] = arg match {
        case (t: Tree[_]) => Some(t.symbol.fullName.toString.split('.').toSeq)
        case sym: Symbol => Some(sym.fullName.toString.split('.').toSeq)
      }
    }
  }

  object ExpressionExtractors {

    object ExIdentifier {
      def unapply(tree: tpd.Tree): Option[(Symbol, tpd.Ident)] = tree match {
        case i: tpd.Ident => Some((i.symbol, i))
        case _ => None
      }
    }

    object ExThis {
      def unapply(tree: tpd.Tree): Option[(Symbol, tpd.This)] = tree match {
        case thiz: tpd.This => Some((thiz.symbol, thiz))
        case _ => None
      }
    }

    object ExTyped {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Typed(e,t) => Some((e, t))
        case _ => None
      }
    }

    object ExLiteral {
      def unapply(tree: tpd.Literal): Boolean = true
    }

    object ExBooleanLiteral {
      def unapply(tree: tpd.Literal): Option[Boolean] = tree match {
        case Literal(Constant(true)) => Some(true)
        case Literal(Constant(false)) => Some(false)
        case _ => None
      }
    }

    object ExCharLiteral {
      def unapply(tree: tpd.Literal): Option[Char] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.CharClass => Some(c.charValue)
        case _ => None
      }
    }

    object ExInt8Literal {
      def unapply(tree: tpd.Literal): Option[Byte] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.ByteClass => Some(c.byteValue)
        case _ => None
      }
    }

    object ExInt16Literal {
      def unapply(tree: tpd.Literal): Option[Short] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.ShortClass => Some(c.shortValue)
        case _ => None
      }
    }

    object ExInt32Literal {
      def unapply(tree: tpd.Literal): Option[Int] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.IntClass => Some(c.intValue)
        case _ => None
      }
    }

    object ExInt64Literal {
      def unapply(tree: tpd.Literal): Option[Long] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.LongClass => Some(c.longValue)
        case _ => None
      }
    }

    object ExBigIntLiteral {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree match {
        case Apply(ExSymbol("scala", "math", "BigInt$", "apply"), Seq(i)) => Some(i)
        case Apply(ExSymbol("stainless", "lang", "package$", "BigInt$", "apply"), Seq(i)) => Some(i)
        case _ => None
      }
    }

    object ExRealLiteral {
      def unapply(tree: tpd.Tree): Option[Seq[tpd.Tree]] = tree match {
        case Apply(ExSymbol("stainless", "lang", "Real$", "apply"), args) => Some(args)
        case _ => None
      }
    }

    object ExUnitLiteral {
      def unapply(tree: tpd.Literal): Boolean = tree match {
        case Literal(c @ Constant(_)) if c.tpe.classSymbol == defn.UnitClass => true
        case _ => false
      }
    }

    /** Returns a string literal from a constant string literal. */
    object ExStringLiteral {
      def unapply(tree: tpd.Tree): Option[String] = tree  match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.StringClass =>
          Some(c.stringValue)
        case _ =>
          None
      }
    }

    object ExThisCall {
      def unapply(tree: tpd.Tree): Option[(ThisType, Symbol, Seq[tpd.Tree], Seq[tpd.Tree])] = {
        val optCall = tree match {
          case id @ Ident(_) => Some((id, Nil, Nil))
          case Apply(id @ Ident(_), args) => Some((id, Nil, args))
          case TypeApply(id @ Ident(_), tps) => Some((id, tps, Nil))
          case Apply(TypeApply(id @ Ident(_), tps), args) => Some((id, tps, args))
          case _ => None
        }

        optCall.flatMap { case (id, tps, args) =>
          id.tpe match {
            case ref @ TermRef(tt: ThisType, _) if !(ref.symbol.owner is Module) =>
              Some((tt, id.symbol, tps, args))
            case _ => None
          }
        }
      }
    }

    object ExLambda {
      def unapply(tree: tpd.Tree): Option[(Seq[tpd.ValDef], tpd.Tree)] = tree match {
        // In `dd`, `paramss` is a List[List[ValDef] | TypeDef]] to represent:
        //   defName[T1, T2, ...](val x_11, x_12, ..)...(val x_n1, val x_n2, ...)
        // If the DefDef in question has type parameters, then the first element of `paramss`
        // is the list of type parameters, otherwise, `paramss` only contains the ValDefs
        // Here, we are interested in only matching a `dd` of the form:
        //   defName(val x_1, val x_2, ...)
        case Block(Seq(dd @ DefDef(_, paramss@List(tpd.ValDefs(valDefs)), _, _)), ExUnwrapped(Closure(Nil, call, _))) if call.symbol == dd.symbol =>
          Some((valDefs, dd.rhs))
        case _ => None
      }
    }

    /** Matches the construct stainless.math.wrapping[A](a) and returns a */
    object ExWrapping {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree  match {
        case Apply(TypeApply(ExSymbol("stainless", "math", "package$", "wrapping"), Seq(_)), tree :: Nil) =>
          Some(tree)
        case _ =>
          None
      }
    }

    // Dotc seems slightly less consistent than scalac: it uses to format for
    // casts. Like scalac, it uses Select for `.toByte`, but it also uses
    // Apply("byte2int", arg) for implicit conversions (and perhaps for other
    // conversions as well).
    object ExCastCall {
      // Returns: (arg, from, to)
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, Type, Type)] = tree match {
        case Apply(Ident(name), List(arg)) =>
          val tmp: Option[(Symbol, Symbol)] = name.toString match {
            case "byte2short" => Some(defn.ByteClass, defn.ShortClass)
            case "byte2int"   => Some(defn.ByteClass, defn.IntClass)
            case "byte2long"  => Some(defn.ByteClass, defn.LongClass)

            case "short2byte" => Some(defn.ShortClass, defn.ByteClass)
            case "short2int"  => Some(defn.ShortClass, defn.IntClass)
            case "short2long" => Some(defn.ShortClass, defn.LongClass)

            case "int2byte"   => Some(defn.IntClass, defn.ByteClass)
            case "int2short"  => Some(defn.IntClass, defn.ShortClass)
            case "int2long"   => Some(defn.IntClass, defn.LongClass)

            case "long2byte"  => Some(defn.LongClass, defn.ByteClass)
            case "long2short" => Some(defn.LongClass, defn.ShortClass)
            case "long2int"   => Some(defn.LongClass, defn.IntClass)

            case _ => None
          }

          tmp map { case (from, to) => (arg, from.info, to.info) }
        case _ => None
      }
    }

    // TODO: Comment (the given comment is a copy/paste from Cbn elim)
    object ExCbnCall {
      /** This phase translates arguments to call-by-name parameters, using the rules
       *
       *      x           ==>    x                  if x is a => parameter
       *      e.apply()   ==>    <cbn-arg>(e)       if e is pure
       *      e           ==>    <cbn-arg>(() => e) for all other arguments
       *
       *  where
       *
       *     <cbn-arg>: [T](() => T): T
       *
       *  is a synthetic method defined in Definitions. Erasure will later strip the <cbn-arg> wrappers.
       */
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree match {
        case Apply(fn, List(arg)) if fn.symbol == defn.cbnArg => arg match {
          case Block(List(anon: tpd.DefDef), _) => Some(anon.rhs)
          case _ =>
            println("TODO: verify what's this: "+arg)
            Some(arg)
        }
        case _ => None
      }
    }

    // TODO: Seems to be useless after all
    // TODO: Comment
    // TODO: Also see how things behave for implicit class not extending anyval and the extension syntax from Scala 3
    // TODO: Refer to transform.ExtensionMethods
    object ExExtensionMethodCall {
      import tpd.TreeOps
      import transform.ExplicitOuter

      def unapply(tree: tpd.Tree)(using cds: ClassDefs): Option[tpd.Tree] = tree match {
        // TODO: method nonEmpty$extension, its symbol is not tagged as an extension method (it's the impl. after all?)
        // TODO: Why ExtMethName and not UniqueExtMethName ??
        // TODO: Also inlines ensuring & al...
        // sym.name.toString.contains("nonEmpty")
        // TODO: What about curried stuff??? The ExCall is likely to pick it up first!!!
        /*case c@ExCall(_, sym, _, _) if (sym.name is NameKinds.ExtMethName) =>
          // val tayst = sym.moduleClass.asClass
          val clsSym = sym.denot.owner.asClass
          val tm = new tpd.TreeMap {
            override def transform(tree: tpd.Tree)(using DottyContext): tpd.Tree = tree match {
              case i@Ident(nme) if nme eq sym.name =>
                val r1 = tpd.desugarIdent(i)
                val r2 = i.underlying
                val dasIchSoll = tpd.ref(clsSym.denot.companionModule).select(nme)
//                val r3 = ExplicitOuter.OuterOps(dottyCtx).path(i, tpd.This(clsSym).tpe.classSymbol)
//                println(r1)
//                println(r2)
//                println(dasIchSoll)
//                println(r3)
                dasIchSoll
              case _ => super.transform(tree)
            }
          }
          // TODO: Il faut replacer ident avec un select sur le module val SetOps
          val res = tm.transform(c)
          // TODO: Yikes
          if (res eq c) None
          else Some(res)*/
        /*
        case Apply(ta@TypeApply(Ident(name), tps), args) if (ta.symbol.name is NameKinds.ExtMethName) =>
          val clsSym = ta.symbol.denot.owner.asClass
//          val res = tpd.TypeApply(clsSym.typeRef, tps)
          ???
        */
        /*
        case c@ExCall(None, sym, tps, args) if (sym.name is NameKinds.ExtMethName) =>
          // TODO: SetOps$ linkedClass gives SetOps, so no?
          val clsSym = sym.denot.owner.asClass
//          val origClassInfo = sym.denot.owner.asClass.classDenot.classInfo
//          val methSym = origClassInfo.decls.lookup(sym.name)
          val clsDef = cds.defs.find(_.symbol eq clsSym).getOrElse(sys.error("TODO"))
          val template = clsDef.rhs.asInstanceOf[tpd.Template]
          val methDef = template.body.collectFirst {
            case d@DefDef(nme, _, _, _) if nme == sym.name => d
          }.getOrElse(sys.error("TODO"))
//          val wot = typer.Inliner.inlineCall(tree)
          val inl = new Inliner(tree, methDef.rhs)
          val res = inl.inlined(tree)
//          val methDef = clsDef.rhs.
          Some(res.asInstanceOf[tpd.Inlined].expansion)
        */
        case _ => None
      }
    }

    object ExCall {
      def unapply(tree: tpd.Tree): Option[(Option[tpd.Tree], Symbol, Seq[tpd.Tree], Seq[tpd.Tree])] = {
        val optCall = tree match {
          case tree @ Ident(_) => Some((None, tree.symbol, Nil, Nil))
          case tree @ Select(qualifier, _) => Some((Some(qualifier), tree.symbol, Nil, Nil))
          case tree @ Apply(id: tpd.Ident, args) => Some((None, id.symbol, Nil, args))
          case tree @ Apply(select @ Select(qualifier, _), args) => Some((Some(qualifier), select.symbol, Nil, args))
          case tree @ TypeApply(id: tpd.Ident, tps) => Some((None, id.symbol, tps, Nil))
          case tree @ TypeApply(select @ Select(qualifier, _), tps) => Some((Some(qualifier), select.symbol, tps, Nil))
          case tree @ Apply(ExCall(caller, sym, tps, args), newArgs) => Some((caller, sym, tps, args ++ newArgs))
          case tree @ TypeApply(ExCall(caller, sym, tps, args), newTps) => Some((caller, sym, tps ++ newTps, args))
          case _ => None
        }

        optCall.map { case (rec, sym, tps, args) =>
          val newRec = rec.filterNot { r =>
            (r.symbol is Module) && !(r.symbol is Case)
          }
          (newRec, sym, tps, args)
        }
      }
    }

    // TODO: review
    object ExClassConstruction {
      def unapply(tree: tpd.Tree): Option[(Type, Seq[tpd.Tree])] = tree match {
        case Apply(Select(New(tpt), nme.CONSTRUCTOR), args) =>
          Some((tpt.tpe, args))

        case Apply(TypeApply(Select(New(tpt), nme.CONSTRUCTOR), _), args) =>
          Some((tree.tpe, args))

        case Apply(e, args) if (
          (e.symbol.owner is Module) &&
          (e.symbol is Synthetic) &&
          (e.symbol.name.toString == "apply")
        ) => Some((tree.tpe, args))

        case Select(s, _) if (tree.symbol is Case) && (tree.symbol is Module) =>
          Some((tree.tpe, Seq()))

        case Ident(_) if (tree.symbol is Case) && (tree.symbol is Module) =>
          Some((tree.tpe, Seq()))

        case _ =>
          None
      }
    }

    object ExTuple {
      def unapply(tree: tpd.Tree): Option[Seq[tpd.Tree]] = tree match {
        case Apply(Select(New(tupleType), nme.CONSTRUCTOR), args) if isTuple(tupleType.symbol, args.size) =>
          Some(args)
        case Apply(TypeApply(Select(ExIdentifier(sym, id), _), _), args) if isTuple(sym, args.size) =>
          Some(args)
        case Apply(TypeApply(Select(
          Apply(TypeApply(ExSymbol("scala", "Predef$", "ArrowAssoc"), Seq(_)), Seq(from)),
          ExNamed("->") | ExNamed("$minus$greater")
        ), Seq(_)), Seq(to)) => Some(Seq(from, to))
        case _ => None
      }
    }

    // TODO: review
    object ExTupleExtract {
      private val Pattern = """_(\d{1,2})""".r

      def unapply(tree: tpd.Tree): Option[(tpd.Tree, Int)] = tree match {
        case Select(tuple @ TupleSymbol(i), ExNamed(Pattern(n))) if n.toInt <= i =>
          Some((tuple, n.toInt))
        case _ => None
      }
    }

    // TODO: review; add other stuff that may miss here
    object ExUnwrapped {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree match {
        case Apply(
            ExSymbol("scala", "Predef$", "Ensuring") |
            ExSymbol("stainless", "lang", "StaticChecks$", "Ensuring"),
            Seq(arg)) => Some(arg)

        case Apply(ExSymbol("stainless", "lang", "package$", "Throwing"), Seq(arg)) => Some(arg)
        case Apply(ExSymbol("stainless", "lang", "package$", "BooleanDecorations"), Seq(arg)) => Some(arg)
        case Apply(ExSymbol("stainless", "lang", "package$", "SpecsDecorations"), Seq(arg)) => Some(arg)
        case Apply(ExSymbol("stainless", "lang", "package$", "StringDecorations"), Seq(arg)) => Some(arg)
        case Apply(ExSymbol("stainless", "lang", "package$", "WhileDecorations"), Seq(arg)) => Some(arg)
        case _ => Some(tree)
      }
    }

    object ExBigIntPattern {
      def unapply(tree: tpd.UnApply): Option[tpd.Literal] = tree match {
        case UnApply(ExSymbol("stainless", "lang", "package$", "BigInt$", "unapply"), _, Seq(l: tpd.Literal)) =>
          Some(l)
        case _ =>
          None
      }
    }

    object ExArrayLiteral {
      def unapply(tree: tpd.Apply): Option[(Type, Seq[tpd.Tree])] = tree match {
        // Array of primitives
        case Apply(ExSymbol("scala", "Array$", "apply"), List(arg, SeqLiteral(args, _))) =>
          tree.tpe match {
            case AppliedType(_, List(t1)) =>
              Some((t1, arg :: args))
            case _ =>
              None
          }

        // Array of objects, which have an extra implicit ClassTag argument (that we do not need)
        case Apply(Apply(TypeApply(ExSymbol("scala", "Array$", "apply"), List(tpt)), List(SeqLiteral(args, _))), ctags) =>
          Some((tpt.tpe, args))

        case Apply(TypeApply(ExSymbol("scala", "Array$", "empty"), List(tpt)), ctags) =>
          Some((tpt.tpe, Nil))

        case _ =>
          None
      }
    }

    object ExNot {
      def unapply(tree: tpd.Select): Option[tpd.Tree] = tree match {
        case Select(t, nme.UNARY_!) if hasBooleanType(t) => Some(t)
        case _ => None
      }
    }

    object ExEquals {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Select(lhs, nme.EQ), List(rhs)) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExNotEquals {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Select(lhs, nme.NE), List(rhs)) => Some((lhs, rhs))
        case _ => None
      }
    }

    object ExUMinus {
      def unapply(tree: tpd.Select): Option[tpd.Tree] = tree match {
        case Select(t, nme.UNARY_-) if hasNumericType(t) => Some(t)
        case _ => None
      }
    }

    object ExBVNot {
      def unapply(tree: tpd.Select): Option[tpd.Tree] = tree match {
        case Select(t, nme.UNARY_~) if hasBVType(t) => Some(t)
        case _ => None
      }
    }

  }

  object StructuralExtractors {
    // TODO: review
    object FrontendBVType {
      val R = """type (UInt|Int)(\d+)""".r

      def unapply(tpe: Type): Option[(Boolean, Int)] = {
        tpe.stripTypeVar match {
          case AppliedType(tr: TypeRef, FrontendBVKind(signed, size) :: Nil) if isBVSym(tr.symbol) =>
            Some((signed, size))
          case tr: TypeRef if isBVSym(tr.symbol) =>
            tr.symbol.toString match {
              case R(signed, size) =>
                Some((signed == "Int", size.toInt))
              case _ =>
                None
            }
          case _ => FrontendBVKind.unapply(tpe)
        }
      }

      def unapply(tr: tpd.Tree): Option[(Boolean, Int)] = unapply(tr.tpe)
    }

    object FrontendBVKind {
      val R = """object ([ui])(\d+)""".r

      def unapply(tpe: Type): Option[(Boolean, Int)] = {
        tpe.stripTypeVar match {
          case tr: TermRef =>
            tr.symbol.toString match {
              case R(signed, size) =>
                Some((signed == "i", size.toInt))
              case _ =>
                None
            }
          case _ =>
            None
        }
      }

      def unapply(tr: tpd.Tree): Option[(Boolean, Int)] = unapply(tr.tpe)
    }

    object ExObjectDef {
      def unapply(td: tpd.TypeDef): Boolean = {
        val sym = td.symbol
        // TODO: not synthetic condition removed, as dotty may generate synthetic object for extension method
        td.isClassDef && ((sym is ModuleClass) || (sym is Package)) && /*!(sym is Synthetic) &&*/ !(sym is Case)
      }
    }

    object ExCaseObject {
      def unapply(s: tpd.Select): Option[Symbol] = {
        if (s.tpe.typeSymbol is ModuleClass) {
          Some(s.tpe.typeSymbol)
        } else {
          None
        }
      }
    }

    object ExClassDef {
      def unapply(td: tpd.TypeDef): Boolean = {
        td.isClassDef
      }
    }

    object ExTypeDef {
      def unapply(td: tpd.TypeDef): Boolean = {
        // TODO: Is it OK if the definition is actually a TypeBoundsTree ?
        !td.isClassDef // && !td.rhs.isInstanceOf[tpd.TypeBoundsTree]
      }
    }

    object ExFunctionDef {
      def unapply(tree: tpd.DefDef): Option[(Symbol, Seq[tpd.TypeDef], Seq[tpd.ValDef], Type, tpd.Tree)] = tree match {
        case dd @ DefDef(name, _, tpt, rhs) if ((
          name != nme.CONSTRUCTOR &&
          !dd.symbol.is(Accessor) &&
          !dd.symbol.is(Synthetic) &&
          !dd.symbol.is(Label)
        ) || (
          (dd.symbol is Synthetic) &&
          canExtractSynthetic(dd.symbol) &&
          !(getAnnotations(tpt.symbol) exists (_._1 == "ignore"))
        )) =>
          Some((dd.symbol, dd.leadingTypeParams, dd.termParamss.flatten, tpt.tpe, dd.rhs))

        case _ => None
      }
    }

    object ExFieldDef {
      /** Matches a definition of a strict field */
      def unapply(tree: tpd.ValDef): Option[(Symbol, Type, tpd.Tree)] = {
        val sym = tree.symbol
        tree match {
          case vd @ ValDef(_, tpt, _) if (
            // TODO: Actually, no?
            // TODO: Comment why it's different from Scalac
            !(sym is CaseAccessor) && !(sym is ParamAccessor) &&
            !(sym is Synthetic) && !(sym is Mutable) && !(sym is Lazy)
          ) => Some((sym, tpt.tpe, vd.rhs))

          case _ => None
        }
      }
    }

    object ExLazyFieldDef {
      /** Matches a definition of a lazy field */
      def unapply(vd: tpd.ValDef): Option[(Symbol, Type, tpd.Tree)] = {
        val sym = vd.symbol
        vd match {
          case ValDef(name, tpt, _) if (
            // TODO: Actually, no?
            // TODO: Comment why it's different from Scalac
            !(sym is CaseAccessor) && !(sym is ParamAccessor) &&
            // Since a lazy can't be mutable, no need to check the Mutable flag.
            !(sym is Synthetic) && (sym is Lazy)
          ) =>
            Some((sym, tpt.tpe, vd.rhs))
          case _ => None
        }
      }
    }

    object ExMutableFieldDef {
      def unapply(tree: tpd.ValDef): Option[(Symbol, Type, tpd.Tree)] = {
        val sym = tree.symbol
        tree match {
          case ValDef(_, tpt, _) if (
            // TODO: Actually, no?
            // TODO: Comment why it's different from Scalac
            !(sym is CaseAccessor) && !(sym is ParamAccessor) &&
            !(sym is Synthetic) && (sym is Mutable)
          ) => Some((sym, tpt.tpe, tree.rhs))

          case _ => None
        }
      }
    }

    object ExDefDefSimple {
      /**
        * Matches against a simple `dd` that may have type parameter and has at most one ValDef clause.
        * That is, `dd` is of the form:
        *     ddName[T1, T2, ...](val x_1, val x_2, ...)
        *           (may be empty)     (may be empty)
        * and not of the general form:
        *     ddName[T1, T2, ...](val x_11, val x_12, ...)(val x_21, val x_22, ...)(...)
        */
      def unapply(dd: tpd.DefDef): Option[(TermName, List[tpd.TypeDef], List[tpd.ValDef], Tree[Type], tpd.Tree)] = dd match {
        case dd@DefDef(name, _, tpt, _) if (dd.termParamss.size <= 1) => // At most one ValDef clause
          Some((name, dd.leadingTypeParams, dd.termParamss.flatten, tpt, dd.rhs))
        case _ => None
      }
    }

    // TODO: il faut spécifier que "Mutable fields in traits or abstract classes cannot have default values"
    // TODO: quid d'une classe qui a une var qui n'est pas ctor-field? dans ce cas, on aura !isCtorField et pas de rhs!!! cela va etre traité comme setter abstrait...
    //    aparamment, leur RHS est ()
    object ExFieldAccessorFunction {
      /** Matches the accessor function of a non-ctor field */
      def unapply(dd: tpd.DefDef): Option[(Symbol, Type, tpd.ValDef, tpd.Tree)] = dd match {
        case ExDefDefSimple(name, _, List(param), tpt, _) if (
          name.isSetterName &&
          (dd.symbol is Accessor) && !(dd.symbol is Lazy)
        ) =>
          val underlying = dd.symbol.underlyingSymbol
          val isCtorField = (underlying is ParamAccessor) || (underlying is CaseAccessor)
          val rhs =
            if (isCtorField && dd.rhs.isEmpty) {
              // tpd.Ident(underlying.termRef)
              val cls = underlying.owner.asClass
              val fieldSel = tpd.Select(tpd.This(cls), underlying.name)
              val paramIdent = tpd.Ident(param.symbol.termRef)
              tpd.Assign(fieldSel, paramIdent)
            }
            else dd.rhs
          Some((dd.symbol, tpt.tpe, param, rhs))
//          if ((underlying is ParamAccessor) || (underlying is CaseAccessor)) None
//          else Some((dd.symbol, tpt.tpe, param, dd.rhs))
        case _ => None
      }
    }
//
//    object ExLazyFieldAccessorFunction {
//      def unapply(dd: tpd.DefDef): Option[(Symbol, Type, tpd.Tree)] = dd match {
//        case ExDefDefSimple(name, _, _, tpt, _) if(
//          name != nme.CONSTRUCTOR &&
//          !(dd.symbol is Synthetic) && (dd.symbol is Accessor) && (dd.symbol is Lazy)
//        ) =>
//          Some((dd.symbol, tpt.tpe, dd.rhs))
//        case _ => None
//      }
//    }

    // TODO: Re-check this
    object ExAssign {
      def unapply(tree: tpd.Assign): Option[(Symbol, tpd.Tree, tpd.Tree)] = tree match {
        // case Assign(sel@Select(This(_), v), rhs) => Some((sel.symbol, sel, rhs))
        case Assign(sel@Select(lhs, _), rhs) => Some((sel.symbol, lhs, rhs))
        case _ => None
      }
    }

    object ExWhile {
      object WithInvariant {
        def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
          case Apply(
            Select(
              Apply(while2invariant, List(rest)),
              invariantSym),
            List(invariant)) if invariantSym.toString == "invariant" => Some((invariant, rest))
          case _ => None
        }
      }

      object WithWeakInvariant {
        def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
          case Apply(
            Select(
              Apply(while2invariant, List(rest)),
              invariantSym),
            List(invariant)) if invariantSym.toString == "noReturnInvariant" => Some((invariant, rest))
          case _ => None
        }
      }

      object WithInline {
        def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree match {
          case Select(
              Apply(_, List(rest)),
              inlineSym
            ) if inlineSym.toString == "inline" => Some(rest)
          case _ => None
        }
      }

      object WithOpaque {
        def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree match {
          case Select(
              Apply(_, List(rest)),
              opaqueSym
            ) if opaqueSym.toString == "opaque" => Some(rest)
          case _ => None
        }
      }

      def parseWhile(tree: tpd.Tree, optInv: Option[tpd.Tree], optWeakInv: Option[tpd.Tree], inline: Boolean, opaque: Boolean):
        Option[(tpd.Tree, tpd.Tree, Option[tpd.Tree], Option[tpd.Tree], Boolean, Boolean)] = {

        tree match {
          case WithOpaque(rest) => parseWhile(rest, optInv, optWeakInv, inline, true)
          case WithInline(rest) => parseWhile(rest, optInv, optWeakInv, true, opaque)
          case WithInvariant(invariant, rest) => parseWhile(rest, Some(invariant), optWeakInv, inline, opaque)
          case WithWeakInvariant(invariant, rest) => parseWhile(rest, optInv, Some(invariant), inline, opaque)
          case WhileDo(cond, body) => Some((cond, body, optInv, optWeakInv, inline, opaque))
          case _ => None
        }
      }

      // returns condition, body, optional invariant and weak invariant, inline boolean, opaque boolean
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree, Option[tpd.Tree], Option[tpd.Tree], Boolean, Boolean)] =
        parseWhile(tree, None, None, false, false)
    }

/*
    object ExWhile {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case WhileDo(cond, body) => Some((cond, body))
        case _ => None
      }
    }

    object ExWhileWithInvariant {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree, tpd.Tree)] = tree match {
        case Apply(
          Select(
            Apply(
              ExSymbol("stainless", "lang", "package$", "WhileDecorations"),
              List(ExWhile(cond, body)),
            ),
            ExNamed("invariant"),
          ),
          List(pred)
        ) => Some((cond, body, pred))
        case _ => None
      }
    }
*/
    /** Extracts the 'require' contract from an expression (only if it's the
      * first call in the block). */
    object ExRequiredExpression {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, Boolean)] = tree match {
        case Apply(ExSymbol("scala", "Predef$", "require"), Seq(body)) =>
          Some((body, false))

        case Apply(ExSymbol("stainless", "lang", "StaticChecks$", "require"), Seq(body)) =>
          Some((body, true))

        case _ => None
      }
    }
    /** Extracts the 'reads' contract from an expression */
    object ExReadsExpression {
      def unapply(tree: tpd.Apply): Option[tpd.Tree] = tree match {
        case Apply(ExSymbol("stainless", "lang", "package$", "reads"), objs :: Nil) =>
          Some(objs)
        case _ => None
      }
    }

    /** Extracts the 'modifies' contract from an expression */
    object ExModifiesExpression {
      def unapply(tree: tpd.Apply): Option[tpd.Tree] = tree match {
        case Apply(ExSymbol("stainless", "lang", "package$", "modifies"), objs :: Nil) =>
          Some(objs)
        case _ => None
      }
    }

    object ExDecreases {
      def unapply(tree: tpd.Apply): Option[Seq[tpd.Tree]] = tree match {
        case Apply(ExSymbol("stainless", "lang", "package$", "decreases"), args) => Some(args)
        case _ => None
      }
    }

    object ExAssertExpression {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, Option[String], Boolean)] = tree match {
        // TODO: Comment
        case Inlined(
          Ident(ExNamed("Predef$")) | Apply(Ident(ExNamed("assert")), _),
          Nil,
          If(
            Select(body, nme.UNARY_!),
            Apply(ExSymbol("scala", "runtime", "Scala3RunTime$", "assertFailed"), args),
            Literal(Constant(()))
          )
        ) =>
          args match {
            case List(Literal(cnst: Constant)) => Some((body, Some(cnst.stringValue), false))
            case _ => Some((body, None, false))
          }

        // This case can happen if we have an assert(expr) where expr can be reduced to false at compile-time.
        case Inlined(
          Ident(ExNamed("Predef$")) | Apply(Ident(ExNamed("assert")), _),
          Nil,
          Apply(ExSymbol("scala", "runtime", "Scala3RunTime$", "assertFailed"), args)
        ) =>
          args match {
            case List(Literal(cnst: Constant)) => Some((tpd.Literal(Constant(false)), Some(cnst.stringValue), false))
            case _ => Some((tpd.Literal(Constant(false)), None, false))
          }

        case Apply(ExSymbol("scala", "Predef$", "assert"), Seq(body)) =>
          Some((body, None, false))

        case Apply(ExSymbol("stainless", "lang", "StaticChecks$", "assert"), Seq(body)) =>
          Some((body, None, true))

        case Apply(ExSymbol("scala", "Predef$", "assert"), Seq(body, Literal(cnst: Constant))) =>
          Some((body, Some(cnst.stringValue), false))

        case Apply(ExSymbol("stainless", "lang", "StaticChecks$", "assert"), Seq(body, Literal(cnst: Constant))) =>
          Some((body, Some(cnst.stringValue), true))

        case _ => None
      }
    }

    // TODO: Ensure (...) that this correctly catch ensure shenanigens
    //  because Ensuring is an implicit class
    object ExEnsuredExpression {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree, Boolean)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("scala", "Predef$", "Ensuring", "ensuring"),
          _, Seq(contract)
        ) => Some((rec, contract, false))

        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "StaticChecks$", "Ensuring", "ensuring"),
          _, Seq(contract)
        ) => Some((rec, contract, true))

        case _ => None
      }
    }

    object ExThrowingExpression {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "package$", "Throwing", "throwing"),
          _, Seq(contract)
        ) => Some((rec, contract))
        case _ => None
      }
    }

    /** Matches the `holds` expression at the end of any boolean expression, and returns the boolean expression.*/
    object ExHoldsExpression {
      def unapply(tree: tpd.Select) : Option[tpd.Tree] = tree match {
        case Select(
          Apply(ExSymbol("stainless", "lang", "package$", "BooleanDecorations"), realExpr :: Nil),
          ExNamed("holds")
        ) => Some(realExpr)
        case _ => None
      }
    }

    /** Matches the `holds` expression at the end of any boolean expression with a proof as argument, and returns both of themn.*/
    object ExHoldsWithProofExpression {
      def unapply(tree: tpd.Apply) : Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Select(Apply(ExSymbol("stainless", "lang", "package$", "BooleanDecorations"), body :: Nil), ExNamed("holds")), proof :: Nil) =>
          Some((body, proof))
        case _ => None
      }
    }

    /*
    object ExHoldsExpression {
      def unapplySeq(tree: tpd.Tree): Option[Seq[tpd.Tree]] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "package$", "BooleanDecorations", "holds"),
          Seq(), args) => Some(rec +: args)
        case _ => None
      }
    }
    */
    /*
    object ExHoldsBecause {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExHoldsExpression(body, Apply(ExSymbol("stainless", "lang", "package$", "because"), Seq(proof))) =>
          Some((body, proof))

        case Apply(
          Select(
            Apply(
              ExSymbol("stainless", "lang" | "proof", "package$", "boolean2ProofOps"),
              List(ExHoldsExpression(body)),
            ),
            ExNamed("because"),
          ),
          List(proof)
        ) =>
          Some((body, proof))

        case _ => None
      }
    }
    */

    /** Matches the `because` method at the end of any boolean expression, and return the assertion and the cause. If no "because" method, still returns the expression */
    object ExMaybeBecauseExpressionWrapper {
      def unapply(tree: tpd.Tree) : Some[tpd.Tree] = tree match {
        case Apply(ExSymbol("stainless", "lang", "package$", "because"), body :: Nil) =>
          unapply(body)
        case body => Some(body)
      }
    }

    /** Matches the `because` method at the end of any boolean expression, and return the assertion and the cause.*/
    object ExBecauseExpression {
      def unapply(tree: tpd.Apply) : Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Select(
          Apply(ExSymbol("stainless", "proof" | "equations", "package$", "boolean2ProofOps"), body :: Nil),
          ExNamed("because")
        ), proof :: Nil) => Some((body, proof))
        case _ => None
      }
    }

    /*object ExBecauseExpression {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "proof" | "equations", "package$", "ProofOps", "because"),
          Seq(), Seq(proof)
        ) =>
          def extract(t: tpd.Tree): Option[tpd.Tree] = t match {
            case Apply(ExSymbol("stainless", "proof" | "equations", "package$", "ProofOps$", "apply"), Seq(body)) => Some(body)
            case Block(Seq(v @ ValDef(_, _, _)), e) => extract(e).filter(_.symbol == v.symbol).map(_ => v.rhs)
            case Inlined(_, members, last) => extract(tpd.Block(members, last))
            case _ => None
          }
          extract(rec).map(_ -> proof)

        case _ =>
          None
      }
    }*/

    object ExComputesExpression {
      // TODO: review
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "package$", "SpecsDecorations", "computes"),
          _, Seq(expected)) => Some((rec, expected))
        case _ => None
      }
    }

    /** Extracts the `(input, output) passes { case In => Out ...}` and returns (input, output, list of case classes) */
    object ExPasses {
      import ExpressionExtractors._

      def unapply(tree: tpd.Apply) : Option[(tpd.Tree, tpd.Tree, List[tpd.CaseDef])] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "package$", "Passes", "passes"),
          _,
          Seq(ExLambda(_, Match(_, cases)))
        ) =>
          def extract(t: tpd.Tree): Option[tpd.Tree] = t match {
            case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "Passes"), _), Seq(body)) =>
              Some(body)
            case _ => None
          }

          extract(rec) flatMap {
            case ExTuple(Seq(in, out)) => Some((in, out, cases))
            case res => None
          }

        case _ => None
      }
    }

    /** Matches the `bigLength` expression at the end of any string expression, and returns the expression.*/
    object ExBigLengthExpression {
      def unapply(tree: tpd.Apply) : Option[tpd.Tree] = tree match {
        case Apply(Select(
          Apply(ExSymbol("stainless", "lang", "package$", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigLength")), Nil)
          => Some(stringExpr)
        case _ => None
      }
    }

    /** Matches the `bigSubstring` method at the end of any string expression, and returns the expression and the start index expression.*/
    object ExBigSubstringExpression {
      def unapply(tree: tpd.Apply) : Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Select(
          Apply(ExSelected("stainless", "lang", "package$", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigSubstring")), startExpr :: Nil)
          => Some(stringExpr, startExpr)
        case _ => None
      }
    }

    /** Matches the `bigSubstring` expression at the end of any string expression, and returns the expression, the start and end index expressions.*/
    object ExBigSubstring2Expression {
      def unapply(tree: tpd.Apply) : Option[(tpd.Tree, tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Select(
          Apply(ExSelected("stainless", "lang", "package$", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigSubstring")), startExpr :: endExpr :: Nil)
          => Some(stringExpr, startExpr, endExpr)
        case _ => None
      }
    }

    object ExErrorExpression {
      def unapply(tree: tpd.Apply) : Option[(String, tpd.Tree)] = tree match {
        case a @ Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "error"), List(tpe)), List(lit : tpd.Literal)) =>
          Some((lit.const.stringValue, tpe))
        case _ =>
          None
      }
    }

    object ExOldExpression {
      def unapply(tree: tpd.Apply): Option[tpd.Tree] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "old"), Seq(_)), Seq(arg)) => Some(arg)
        case _ => None
      }
    }

    object ExSnapshotExpression {
      def unapply(tree: tpd.Apply): Option[tpd.Tree] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "snapshot"), Seq(_)), Seq(arg)) => Some(arg)
        case _ => None
      }
    }

    object ExFreshCopyExpression {
      def unapply(tree: tpd.Apply) : Option[tpd.Tree] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "freshCopy"), List(_)), List(arg)) =>
          Some(arg)
        case _ =>
          None
      }
    }

    // TODO: Verify
    /** Matches the construct int2bigInt(a) and returns a */
    object ExIntToBigInt {
      // TODO: In Scalac, no 'scala' prefix
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree match {
        case Apply(ExSymbol("scala", "math", "BigInt$", "int2bigInt"), List(t)) => Some(t)
        case _ => None
      }
    }

    // TODO: Verify
    /** `intToBV` extraction */
    object ExIntToBV {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree  match {
        case Apply(
          TypeApply(
            ExSymbol("stainless", "math", "BitVectors$", "intToBV"),
            typ :: Nil
          ), n :: Nil
        ) =>
          Some((typ, n))
        case _ =>
          None
      }
    }

    // TODO: Verify
    /** `bigIntToBV` extraction */
    object ExBigIntToBV {
      def unapply(tree: tpd.Tree): Option[(Boolean, Int, tpd.Tree)] = tree  match {
        case Apply(
          TypeApply(
          ExSymbol("stainless", "math", "BitVectors$", "bigIntToBV"),
            FrontendBVKind(signed, size) :: Nil
          ), n :: Nil
        ) =>
          Some((signed, size, n))
        case _ =>
          None
      }
    }

    // TODO: Verify
    /** `max` extraction for bitvectors */
    object ExMaxBV {
      def unapply(tree: tpd.Tree): Option[(Boolean, Int)] = tree  match {
        case TypeApply(
        ExSymbol("stainless", "math", "BitVectors$", "max"),
          FrontendBVType(signed, size) :: Nil
        ) =>
          Some((signed, size))
        case _ =>
          None
      }
    }

    // TODO: Verify
    /** `min` extraction for bitvectors */
    object ExMinBV {
      def unapply(tree: tpd.Tree): Option[(Boolean, Int)] = tree  match {
        case TypeApply(
        ExSymbol("stainless", "math", "BitVectors$", "min"),
          FrontendBVType(signed, size) :: Nil
        ) =>
          Some((signed, size))
        case _ =>
          None
      }
    }

    // TODO: Verify
    /** `fromByte` extraction (Byte to Int8 identity conversion) */
    object ExFromByte {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree  match {
        case Apply(
          ExSymbol("stainless", "math", "BitVectors$", "fromByte"),
          expr :: Nil
        ) =>
          Some(expr)
        case _ =>
          None
      }
    }

    // TODO: Verify
    /** `fromShort` extraction (Short to Int16 identity conversion) */
    object ExFromShort {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree  match {
        case Apply(
          ExSymbol("stainless", "math", "BitVectors$", "fromShort"),
          expr :: Nil
        ) =>
          Some(expr)
        case _ =>
          None
      }
    }

    // TODO: Verify
    /** `fromInt` extraction (Int to Int32 identity conversion) */
    object ExFromInt {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree  match {
        case Apply(
          ExSymbol("stainless", "math", "BitVectors$", "fromInt"),
          expr :: Nil
        ) =>
          Some(expr)
        case _ =>
          None
      }
    }

    // TODO: Verify
    /** `fromLong` extraction (Long to Int64 identity conversion) */
    object ExFromLong {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree  match {
        case Apply(
          ExSymbol("stainless", "math", "BitVectors$", "fromLong"),
          expr :: Nil
        ) =>
          Some(expr)
        case _ =>
          None
      }
    }

    // TODO: Verify (some diff. with scalac)
    object ExChooseExpression {
      def unapply(tree: tpd.Apply) : Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "choose"), List(tpt)), Seq(pred)) =>
          Some((tpt, pred))
        case _ => None
      }
    }

    // TODO: Verify
    object ExSwapExpression {
      def unapply(tree: tpd.Apply) : Option[(tpd.Tree, tpd.Tree, tpd.Tree, tpd.Tree)] = tree match {
        case Apply(
          TypeApply(ExSymbol("stainless", "lang", "package$", "swap"), _),
          array1 :: index1 :: array2 :: index2 :: Nil) =>
          Some((array1, index1, array2, index2))
        case _ => None
      }
    }

    // TODO: Verify (some diff. with scalac)
    object ExForallExpression {
      def unapply(tree: tpd.Apply) : Option[tpd.Tree] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "forall"), _), List(fun)) =>
          Some(fun)
        case _ => None
      }
    }

    // TODO: Verify
    object ExMutableMapWithDefault {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree, tpd.Tree)] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "MutableMap$", "withDefaultValue"), List(tptFrom, tptTo)), List(default)) =>
          Some(tptFrom, tptTo, default)
        case _ => None
      }
    }

    // TODO: Verify
    object ExFiniteMap {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree, List[tpd.Tree])] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "Map$", "apply"), List(tptFrom, tptTo)), args) =>
          Some((tptFrom, tptTo, args))
        case _ => None
      }
    }

    // TODO: Verify
    object ExFiniteSet {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree,List[tpd.Tree])] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "Set$", "apply"), List(tpt)), args) =>
          Some(tpt, args)
        case _ => None
      }
    }

    // TODO: Verify
    object ExFiniteBag {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, List[tpd.Tree])] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "Bag$", "apply"), List(tpt)), args) =>
          Some(tpt, args)
        case _ => None
      }
    }

    // TODO: Verify
    private object ExArraySelect {
      def unapply(tree: tpd.Select): Option[(tpd.Tree, String)] = tree match {
        case Select(array, select) if isArrayClassSym(array.tpe.typeSymbol) => Some((array, select.toString))
        case _ => None
      }
    }

    // TODO: Verify
    object ExArrayUpdate {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree, tpd.Tree)] = tree match {
        // This implicit conversion to ArrayOps is shadowed. We therefore skip it here.
        case Apply(ExArraySelect(array, "update"), Seq(index, newValue)) => Some((array, index, newValue))
        case _ => None
      }
    }

    // TODO: Verify
    object ExArrayApply {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree)] = tree match {
        // This implicit conversion to ArrayOps is shadowed. We therefore skip it here.
        case Apply(ExArraySelect(array, "apply"), Seq(index)) => Some((array, index))
        case _ => None
      }
    }

    // TODO: Verify
    object ExArrayFill {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Apply(Apply(TypeApply(ExSymbol("scala", "Array$", "fill"), List(baseType)), List(length)), List(dflt)), _) =>
          Some((baseType, length, dflt))

        case _ => None
      }
    }

    // TODO: Verify
    object ExArrayApplyBV {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree, tpd.Tree)] = tree match {
        case Apply(TypeApply(
          Select(
            Apply(
              // TODO: Check if it's ArrayIndexing or ArrayIndexing$
              TypeApply(ExSymbol("stainless", "math", "BitVectors$", "ArrayIndexing"), tpe :: Nil),
              array :: Nil
            ),
            ExNamed("apply")
          ),
          bvType :: Nil),
          index :: Nil) =>

          Some((array, bvType, index))

        case _ => None
      }
    }

    // TODO: Verify
    object ExArrayUpdated {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Apply(
          TypeApply(Select(Apply(ExSymbol("scala", "Predef$", s), List(lhs)), ExNamed("updated")), _),
          List(index, value)), List(Apply(_, _))) if s.toString contains "Array" =>
          Some((lhs, index, value))

        case Apply(
          Select(
            Apply(
              TypeApply(ExSymbol("stainless", "lang", "package$", "ArrayUpdating"), tpe :: Nil),
              array :: Nil
            ),
            ExNamed("updated")
          ), index :: value :: Nil) =>
          Some((array, index, value))

        case _ => None
      }
    }

    // TODO: Verify
    /**
     * Extract both Array.length and Array.size as they are equivalent.
     *
     * Note that Array.size is provided thought implicit conversion to
     * scala.collection.mutable.ArrayOps via scala.Predef.*ArrayOps.
     * As such, `arrayOps` can be `intArrayOps`, `genericArrayOps`, etc...
     */
    object ExArrayLength {
      def unapply(tree: tpd.Select): Option[tpd.Tree] = tree match {
        case Select(Apply(ExSymbol("scala", "Predef$", s), List(lhs)), ExNamed("size")) if s.toString contains "Array" =>
          Some(lhs)

        case ExArraySelect(array, "length") => Some(array)

        case _ => None
      }
    }

    // TODO: Verify
    /** Matches the construct List[tpe](a, b, ...) and returns tpe and arguments */
    object ExListLiteral {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, List[tpd.Tree])] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "collection", "List$", "apply"), List(tpt)), args) =>
          Some((tpt, args))
        case _ =>
          None
      }
    }

    // TODO: Verify
    /** Matches an implication `lhs ==> rhs` and returns (lhs, rhs)*/
    object ExImplies {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Select(
          lhs@ExSymbol("stainless", "lang", "package$", "BooleanDecorations"),
          ExNamed("==>") | ExNamed("$eq$eq$greater")), List(rhs)) =>
          Some((lhs, rhs))
        case _ =>
          None
      }
    }

    // TODO: Verify
    /** Matches `lhs &&& rhs` and returns (lhs, rhs)*/
    object ExSplitAnd {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Select(
          lhs@ExSymbol("stainless", "lang", "package$", "BooleanDecorations"),
          ExNamed("&&&") | ExNamed("$amp$amp$amp")), List(rhs)) =>
          Some((lhs, rhs))
        case _ =>
          None
      }
    }

    object ExIndexedAt {
      def unapply(annot: Annotation): Option[tpd.Tree] = annot match {
        case ConcreteAnnotation(
          Apply(Select(New(ExSymbol("stainless", "annotation", "indexedAt")), _), List(arg))
        ) => Some(arg)
        case _ => None
      }
    }
  }

  object ExIdentity {
    def unapply(tree: tpd.Apply): Option[tpd.Tree] = tree match {
      case Apply(TypeApply(ExSymbol("scala", "Predef$", "identity"), Seq(_)), Seq(body)) =>
        Some(body)
      case Apply(TypeApply(ExSymbol("scala", "Predef$", "locally"), Seq(_)), Seq(body)) =>
        Some(body)
      case _ => None
    }
  }
}
