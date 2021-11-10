package stainless
package frontends.dotc


import scala.quoted._
import scala.tasty.inspector._

trait TastyTayst(using val q: Quotes) {
  import quotes._
  import quotes.reflect._
  import Flags._

  def classFromName(nameStr: String): Symbol = Symbol.requiredClass(nameStr) // TODO: Typename missing
  def moduleFromName(nameStr: String): Symbol = Symbol.requiredModule(nameStr) // TODO: Typename missing; TODO: Was TermSymbol


  def getAnnotations(sym: Symbol, ignoreOwner: Boolean = false): Seq[(String, Seq[Tree])] = {
    if (sym == Symbol.noSymbol)
      return Seq.empty

    // TODO: isEffectivelyErased
    val erased = Seq.empty[(String, Seq[Tree])] // if (sym.isEffectivelyErased) Seq(("ghost", Seq.empty[Tree])) else Seq()
    val selfs = sym.annotations
    val owners =
      if (ignoreOwner) List.empty[Term]
      else sym.owner.annotations.filter(annot =>
        annot.toString != "stainless.annotation.export" &&
          !annot.toString.startsWith("stainless.annotation.cCode.global")
      )
    val companions = List(sym.companionModule).filter(_ != Symbol.noSymbol).flatMap(_.annotations)
    erased ++ (for {
      a <- selfs ++ owners ++ companions
      name = a.symbol.fullName
        .replace(".package.", ".")
    } yield {
      def args = a match {
        case Apply(_, args) => args
        case _ => Nil
      }
      if (name startsWith "stainless.annotation.") {
        val shortName = name drop "stainless.annotation.".length
        Some((shortName, args))
      } else if (name == "inline" || name == "scala.inline") {
        Some(("inline", args))
      } else {
        None
      }
    }).flatten.foldLeft[(Set[String], Seq[(String, Seq[Tree])])]((Set(), Seq())) {
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
    private val cache = scala.collection.mutable.Map[Symbol, Option[Int]]()
    private val cardinality = """Tuple(\d{1,2})""".r
    def unapply(sym: Symbol): Option[Int] = cache.getOrElse(sym, {
      // First, extract a guess about the cardinality of the Tuple.
      // Then, confirm that this is indeed a regular Tuple.
      // TODO
      val name: String = ??? // sym.originalName.toString
      val res = name match {
        case cardinality(i) if isTuple(sym, i.toInt) => Some(i.toInt)
        case _ => None
      }

      cache(sym) = res
      res
    })

    // TODO
    // TODO: same type after erasure
    // def unapply(tpe: TypeRepr): Option[Int] = ??? // tpe.classSymbols.collectFirst { case TupleSymbol(i) => i }

    // def unapply(tree: Tree): Option[Int] = unapply(tree.tpe)
  }

  def isBigIntSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) == bigIntSym

  def isStringSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) match { case `stringSym` => true case _ => false }

  //  def isByNameSym(sym : Symbol) : Boolean = getResolvedTypeSym(sym) == byNameSym

  // Resolve type aliases
  def getResolvedTypeSym(sym: Symbol): Symbol = {
    if (sym.isAliasType) {
      // TODO
      ???
//      getResolvedTypeSym(sym.info.resultType.typeSymbol)
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

  // TODO
  def hasIntType(t: Tree): Boolean = {
    ???
    // val tpe = t.tpe.widen
//    t.tpe frozen_<:< defn.IntClass.info
  }

  // TODO
  def hasBigIntType(t: Tree): Boolean = ??? // isBigIntSym(t.tpe.typeSymbol)

  // TODO
  def hasStringType(t: Tree): Boolean = ??? // isStringSym(t.tpe.typeSymbol)

  // TODO
  private lazy val bvtypes: Set[TypeRepr] = ??? // Set(defn.ByteType, defn.ShortType, defn.IntType, defn.LongType)

  // TODO
  def hasBVType(t: Tree): Boolean = ??? // bvtypes.exists(bv => t.tpe/*.widen*/ frozen_<:< bv)

  def hasNumericType(t: Tree): Boolean = hasBigIntType(t) || hasBVType(t) || hasRealType(t)

  // TODO
  def hasRealType(t: Tree): Boolean = ??? // isRealSym(t.tpe.typeSymbol)

  // TODO
  def hasBooleanType(t: Tree): Boolean = ??? // t.tpe/*.widen*/ frozen_<:< defn.BooleanType

  def isDefaultGetter(sym: Symbol): Boolean = {
    // TODO
    (sym.flags is Synthetic) && ??? // sym.name.isTermName && sym.name.toTermName.toString.contains("$default$")
  }

  def isCopyMethod(sym: Symbol): Boolean = {
    // TODO
    (sym.flags is Synthetic) && ??? // sym.name.isTermName && sym.name.toTermName.toString.startsWith("copy")
  }

  def canExtractSynthetic(sym: Symbol): Boolean = {
    (sym.flags is Implicit) ||
      isDefaultGetter(sym) ||
      isCopyMethod(sym)
  }

  object ExSelected {
    def unapplySeq(select: Select): Option[Seq[String]] = {
      select match {
        case Select(This(tname), name) =>
          Some(Seq(tname.toString, name.toString))
        case Select(from: Select, name) =>
          unapplySeq(from).map(seq => seq :+ name.toString)
        case Select(from: Ident, name) =>
          Some(Seq(from.toString, name.toString))
        case _ => None
      }
    }
  }

  // TODO
//    object ExNamed {
//      def unapply(name: Name): Option[String] = Some(name.toString)
//    }

  object ExSymbol {
    // TODO: Cannot be tested at runtime
    def unapplySeq(arg: Any): Option[Seq[String]] = arg match {
      case (t: Tree) => Some(t.symbol.fullName.toString.split('.').toSeq)
      case sym: Symbol => Some(sym.fullName.toString.split('.').toSeq)
    }
  }

  object ExIdentifier {
    def unapply(tree: Tree): Option[(Symbol, Ident)] = tree match {
      case i: Ident => Some((i.symbol, i))
      case _ => None
    }
  }

  object ExThis {
    def unapply(tree: Tree): Option[(Symbol, This)] = tree match {
      case thiz: This => Some((thiz.symbol, thiz))
      case _ => None
    }
  }

  object ExTyped {
    def unapply(tree: Tree): Option[(Tree, Tree)] = tree match {
      case Typed(e,t) => Some((e, t))
      case _ => None
    }
  }

  // TODO: Say for things such as Int.MaxValue etc
  object ExEffectivelyLiteral {
    def unapply(tree: Tree): Option[Literal] = tree match {
      case sel@Select(Ident(_), _) =>
//        sel.symbol.info match {
//          case ExprType(ConstantType(c)) => Some(Literal(c))
//          case ConstantType(c) => Some(Literal(c))
//          case _ => None
//        }
        // TODO
        ???
      case _ => None
    }
  }
/*
  object ExBooleanLiteral {
    def unapply(tree: Literal): Option[Boolean] = tree match {
      case Literal(Constant(true)) => Some(true)
      case Literal(Constant(false)) => Some(false)
      case _ => None
    }
  }

  object ExCharLiteral {
    def unapply(tree: Literal): Option[Char] = tree match {
      case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.CharClass => Some(c.charValue)
      case _ => None
    }
  }
*/

  object ExThisCall {
    def unapply(tree: Tree): Option[(ThisType, Symbol, Seq[Tree], Seq[Tree])] = {
      val optCall = tree match {
        case id @ Ident(_) => Some((id, Nil, Nil))
        case Apply(id @ Ident(_), args) => Some((id, Nil, args))
        case TypeApply(id @ Ident(_), tps) => Some((id, tps, Nil))
        case Apply(TypeApply(id @ Ident(_), tps), args) => Some((id, tps, args))
        case _ => None
      }
      // TODO
      /*
      optCall.flatMap { case (id, tps, args) =>
        id.tpe match {
          case ref @ TermRef(tt: ThisType, _) if !(ref.symbol.owner is Module) =>
            Some((tt, id.symbol, tps, args))
          case _ => None
        }
      }
      */
      ???
    }
  }

  object ExLambda {
    // TODO
    def unapply(tree: Tree): Option[(Seq[ValDef], Tree)] = tree match {
      // In `dd`, `paramss` is a List[List[ValDef] | TypeDef]] to represent:
      //   defName[T1, T2, ...](val x_11, x_12, ..)...(val x_n1, val x_n2, ...)
      // If the DefDef in question has type parameters, then the first element of `paramss`
      // is the list of type parameters, otherwise, `paramss` only contains the ValDefs
      // Here, we are interested in only matching a `dd` of the form:
      //   defName(val x_1, val x_2, ...)
      /*case Block(Seq(dd @ DefDef(_, paramss@List(ValDefs(valDefs)), _, _)), ExUnwrapped(Closure(Nil, call, _))) if call.symbol == dd.symbol =>
        Some((valDefs, dd.rhs))*/
      case _ => None
    }
  }

  /** Matches the construct stainless.math.wrapping[A](a) and returns a */
  object ExWrapping {
    def unapply(tree: Tree): Option[Tree] = tree  match {
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
    def unapply(tree: Tree): Option[(Tree, TypeRepr, TypeRepr)] = tree match {
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
        // TODO
        ???
//        tmp map { case (from, to) => (arg, from.info, to.info) }
      case _ => None
    }
  }

  object ExCall {
    def unapply(tree: Tree): Option[(Option[Tree], Symbol, Seq[Tree], Seq[Tree])] = {
      val optCall = tree match {
        case tree @ Ident(_) => Some((None, tree.symbol, Nil, Nil))
        case tree @ Select(qualifier, _) => Some((Some(qualifier), tree.symbol, Nil, Nil))
        case tree @ Apply(id: Ident, args) => Some((None, id.symbol, Nil, args))
        case tree @ Apply(select @ Select(qualifier, _), args) => Some((Some(qualifier), select.symbol, Nil, args))
        case tree @ TypeApply(id: Ident, tps) => Some((None, id.symbol, tps, Nil))
        case tree @ TypeApply(select @ Select(qualifier, _), tps) => Some((Some(qualifier), select.symbol, tps, Nil))
        case tree @ Apply(ExCall(caller, sym, tps, args), newArgs) => Some((caller, sym, tps, args ++ newArgs))
        case tree @ TypeApply(ExCall(caller, sym, tps, args), newTps) => Some((caller, sym, tps ++ newTps, args))
        case _ => None
      }

      optCall.map { case (rec, sym, tps, args) =>
        val newRec = rec.filterNot { r =>
          (r.symbol.flags is Module) && !(r.symbol.flags is Case)
        }
        (newRec, sym, tps, args)
      }
    }
  }

  // TODO: review
  object ExClassConstruction {
    def unapply(tree: Tree): Option[(TypeRepr, Seq[Tree])] = tree match {
      case Apply(Select(New(tpt), "<init>"/*nme.CONSTRUCTOR*/), args) =>
        Some((tpt.tpe, args))

      case app@Apply(TypeApply(Select(New(tpt), "<init>" /*nme.CONSTRUCTOR*/), _), args) =>
        Some((app.tpe, args))

      case app@Apply(e, args) if (
        (e.symbol.owner.flags is Module) &&
          (e.symbol.flags is Synthetic) &&
          (e.symbol.name.toString == "apply")
        ) => Some((app.tpe, args))

      case sel@Select(s, _) if (tree.symbol.flags is Case) && (tree.symbol.flags is Module) =>
        Some((sel.tpe, Seq()))

      case idt@Ident(_) if (tree.symbol.flags is Case) && (tree.symbol.flags is Module) =>
        Some((idt.tpe, Seq()))

      case _ =>
        None
    }
  }

  object ExTuple {
    def unapply(tree: Tree): Option[Seq[Tree]] = tree match {
      case Apply(Select(New(tupleType), "<init>"/*nme.CONSTRUCTOR*/), args) if isTuple(tupleType.symbol, args.size) =>
        Some(args)
      case Apply(TypeApply(Select(ExIdentifier(sym, id), _), _), args) if isTuple(sym, args.size) =>
        Some(args)
      case Apply(TypeApply(Select(
        Apply(TypeApply(ExSymbol("scala", "Predef$", "ArrowAssoc"), Seq(_)), Seq(from)),
        "->" | "$minus$greater"
      ), Seq(_)), Seq(to)) => Some(Seq(from, to))
      case _ => None
    }
  }

  // TODO: review
  object ExTupleExtract {
    private val Pattern = """_(\d{1,2})""".r

    def unapply(tree: Tree): Option[(Tree, Int)] = tree match {
      case Select(tuple @ TupleSymbol(i), Pattern(n)) if n.toInt <= i =>
        Some((tuple, n.toInt))
      case _ => None
    }
  }

  // TODO: review; add other stuff that may miss here
  object ExUnwrapped {
    def unapply(tree: Tree): Option[Tree] = tree match {
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
    def unapply(tree: Unapply): Option[Literal] = tree match {
      case Unapply(ExSymbol("stainless", "lang", "package$", "BigInt$", "unapply"), _, Seq(l: Literal)) =>
        Some(l)
      case _ =>
        None
    }
  }

  object ExArrayLiteral {
    def unapply(tree: Apply): Option[(TypeRepr, Seq[Tree])] = tree match {
      // TODO: SeqLiteral
//      // Array of primitives
//      case Apply(ExSymbol("scala", "Array$", "apply"), List(arg, Typed(SeqLiteral(args, _), _))) =>
//        tree.tpe match {
//          case AppliedType(_, List(t1)) =>
//            Some((t1, arg :: args))
//          case _ =>
//            None
//        }

      // TODO: SeqLiteral
//      // Array of objects, which have an extra implicit ClassTag argument (that we do not need)
//      case Apply(Apply(TypeApply(ExSymbol("scala", "Array$", "apply"), List(tpt)), List(Typed(SeqLiteral(args, _), _))), ctags) =>
//        Some((tpt.tpe, args))

      case Apply(TypeApply(ExSymbol("scala", "Array$", "empty"), List(tpt)), ctags) =>
        Some((tpt.tpe, Nil))

      case _ =>
        None
    }
  }

  object ExNot {
    def unapply(tree: Select): Option[Tree] = tree match {
      case Select(t, "unary_!") if hasBooleanType(t) => Some(t)
      case _ => None
    }
  }

  object ExEquals {
    def unapply(tree: Apply): Option[(Tree, Tree)] = tree match {
      case Apply(Select(lhs, "=="), List(rhs)) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExNotEquals {
    def unapply(tree: Apply): Option[(Tree, Tree)] = tree match {
      case Apply(Select(lhs, "!="), List(rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object ExUMinus {
    def unapply(tree: Select): Option[Tree] = tree match {
      case Select(t, "unary_-") if hasNumericType(t) => Some(t)
      case _ => None
    }
  }

  object ExBVNot {
    def unapply(tree: Select): Option[Tree] = tree match {
      case Select(t, "unary_~") if hasBVType(t) => Some(t)
      case _ => None
    }
  }

  // TODO: review
  object FrontendBVType {
    val R = """type (UInt|Int)(\d+)""".r

    def unapply(tpe: TypeRepr): Option[(Boolean, Int)] = {
      // TODO: stripTypeVar
      tpe match {
        case AppliedType(tr: TypeRef, FrontendBVKind(signed, size) :: Nil) if isBVSym(tr.typeSymbol) => // TODO: symbol ~> typeSymbol
          Some((signed, size))
        case tr: TypeRef if isBVSym(tr.typeSymbol) =>// TODO: symbol ~> typeSymbol
          tr.typeSymbol.toString match { // TODO: symbol ~> typeSymbol
            case R(signed, size) =>
              Some((signed == "Int", size.toInt))
            case _ =>
              None
          }
        case _ => FrontendBVKind.unapply(tpe)
      }
    }
    // TODO
    // def unapply(tr: Tree): Option[(Boolean, Int)] = unapply(tr.tpe)
  }

  object FrontendBVKind {
    val R = """object ([ui])(\d+)""".r

    def unapply(tpe: TypeRepr): Option[(Boolean, Int)] = {
      // TODO: stripTypeVar
      tpe match {
        case tr: TermRef =>
          tr.typeSymbol.toString match { // TODO: symbol ~> typeSymbol
            case R(signed, size) =>
              Some((signed == "i", size.toInt))
            case _ =>
              None
          }
        case _ =>
          None
      }
    }

    // TODO: Double definition after erasure
    // def unapply(tr: Tree): Option[(Boolean, Int)] = unapply(tr.tpe)
  }

  object ExObjectDef {
    def unapply(td: TypeDef): Boolean = {
      val sym = td.symbol
      // TODO: not synthetic condition removed, as dotty may generate synthetic object for extension method
      sym.isClassDef && ((sym.flags is Module) || (sym.flags is Package)) && /*!(sym is Synthetic) &&*/ !(sym.flags is Case) // TODO: ModuleClass ~> Module
    }
  }

  object ExCaseObject {
    def unapply(s: Select): Option[Symbol] = {
      if (s.tpe.typeSymbol.flags is Module) { // TODO: ModuleClass ~> Module
        Some(s.tpe.typeSymbol)
      } else {
        None
      }
    }
  }

  object ExClassDef {
    def unapply(td: TypeDef): Boolean = {
      td.symbol.isClassDef
    }
  }

  object ExTypeDef {
    def unapply(td: TypeDef): Boolean = {
      // TODO: Is it OK if the definition is actually a TypeBoundsTree ?
      !td.symbol.isClassDef // && !td.rhs.isInstanceOf[TypeBoundsTree]
    }
  }

  object ExFunctionDef {
    // TODO: Rhs is an Option[Term], not a Tree
    def unapply(tree: DefDef): Option[(Symbol, Seq[TypeDef], Seq[ValDef], TypeRepr, Option[Term])] = tree match {
      case dd @ DefDef(name, _, tpt, rhs) if ((
        name != "<init>" &&
        !dd.symbol.flags.is(FieldAccessor) && // TODO: Accessor ~> FieldAccessor
        !dd.symbol.flags.is(Synthetic) /*&&
        !dd.symbol.flags.is(Label)*/ // TODO: No such thing as label
      ) || (
        (dd.symbol.flags is Synthetic) &&
        canExtractSynthetic(dd.symbol) &&
        !(getAnnotations(tpt.symbol) exists (_._1 == "ignore"))
      )) =>
        val valDefs = dd.termParamss.flatMap {
          case TermParamClause(vds) => vds
        }
        Some((dd.symbol, dd.leadingTypeParams, valDefs, tpt.tpe, rhs))

      case _ => None
    }
  }

  object ExCtorFieldDef {
    /** Matches a definition of a strict and immutable field that is part of the constructor parameters. */
    def unapply(vd: ValDef): Option[(Symbol, TypeRepr, Option[Term])] = { // TODO: ValDef rhs is not a Tree
      val sym = vd.symbol
      vd match {
        case ValDef(_, tpt, rhs) if
          ((sym.flags is CaseAccessor) || (sym.flags is ParamAccessor)) &&
          !(sym.flags is Synthetic) && !(sym.flags is Mutable) // Note: Check for not being lazy omitted because a ctor field cannot be lazy
          => Some((sym, tpt.tpe, rhs))

        case _ => None
      }
    }
  }

  object ExCtorMutableFieldDef {
    /** Matches a definition of a strict and mutable field that is part of the constructor parameters. */
    def unapply(vd: ValDef): Option[(Symbol, TypeRepr, Option[Term])] = {
      val sym = vd.symbol
      vd match {
        case ValDef(_, tpt, rhs) if
          ((sym.flags is CaseAccessor) || (sym.flags is ParamAccessor)) &&
          !(sym.flags is Synthetic) && (sym.flags is Mutable)
          => Some((sym, tpt.tpe, rhs))

        case _ => None
      }
    }
  }

  object ExNonCtorFieldDef {
    /** Matches a definition of a strict and immutable field that is not part of the constructor parameters. */
    def unapply(vd: ValDef): Option[(Symbol, TypeRepr, Option[Term])] = {
      val sym = vd.symbol
      vd match {
        case ValDef(_, tpt, rhs) if
          !(sym.flags is CaseAccessor) && !(sym.flags is ParamAccessor) &&
          !(sym.flags is Synthetic) && !(sym.flags is Mutable) && !(sym.flags is Lazy)
          => Some((sym, tpt.tpe, rhs))

        case _ => None
      }
    }
  }

  object ExNonCtorMutableFieldDef {
    def unapply(vd: ValDef): Option[(Symbol, TypeRepr, Option[Term])] = {
      val sym = vd.symbol
      vd match {
        case ValDef(_, tpt, rhs) if
          !(sym.flags is CaseAccessor) && !(sym.flags is ParamAccessor) &&
          // Since a lazy can't be mutable (and vice-versa), we do not need to check the Mutable flag.
          !(sym.flags is Synthetic) && (sym.flags is Mutable)
          => Some((sym, tpt.tpe, rhs))

        case _ => None
      }
    }
  }

  object ExLazyFieldDef {
    /** Matches a definition of a lazy field */
    def unapply(vd: ValDef): Option[(Symbol, TypeRepr, Option[Term])] = {
      val sym = vd.symbol
      vd match {
        case ValDef(_, tpt, rhs) if
          !(sym.flags is CaseAccessor) && !(sym.flags is ParamAccessor) &&
          !(sym.flags is Synthetic) && (sym.flags is Lazy)
          => Some((sym, tpt.tpe, rhs))
        case _ => None
      }
    }
  }

}
