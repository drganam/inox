/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import utils._
import org.apache.commons.lang3.StringEscapeUtils
import scala.language.implicitConversions

object optPrintPositions extends FlagOptionDef("print-positions", false)
object optPrintUniqueIds extends FlagOptionDef("print-ids",       false)
object optPrintTypes     extends FlagOptionDef("print-types",     false)
object optPrintUnicode   extends FlagOptionDef("print-unicode",   false)

trait Printers { self: Trees =>

  val printer: Printer { val trees: self.type }

  case class PrinterContext(current: Tree,
                            parents: List[Tree],
                            lvl: Int,
                            opts: PrinterOptions,
                            sb: StringBuffer = new StringBuffer) {

    def parent = parents.headOption
  }

  case class PrinterOptions(baseIndent: Int = 0,
                            printPositions: Boolean = false,
                            printUniqueIds: Boolean = false,
                            printTypes: Boolean = false,
                            printChooses: Boolean = false,
                            printUnicode: Boolean = false,
                            symbols: Option[Symbols] = None) {
    require(
      !printTypes || symbols.isDefined,
      "Can't print types without an available symbol table"
    )
  }

  object PrinterOptions {
    def fromContext(ctx: Context, symbols: Option[Symbols] = None): PrinterOptions = {
      PrinterOptions(
        baseIndent = 0,
        printPositions = ctx.options.findOptionOrDefault(optPrintPositions),
        printUniqueIds = ctx.options.findOptionOrDefault(optPrintUniqueIds),
        printTypes = ctx.options.findOptionOrDefault(optPrintTypes) && symbols.isDefined,
        printChooses = ctx.options.findOptionOrDefault(optPrintChooses),
        printUnicode = ctx.options.findOptionOrDefault(optPrintUnicode),
        symbols = symbols
      )
    }

    def fromSymbols(s: Symbols, ctx: Context): PrinterOptions = {
      fromContext(ctx, symbols = Some(s))
    }
  }

  trait Printable {
    def asString(using opts: PrinterOptions): String
  }

  def asString(obj: Any)(using opts: PrinterOptions): String = obj match {
    case tree: Tree => prettyPrint(tree, opts)
    case id: Identifier => id.asString
    case _ => obj.toString
  }

  def prettyPrint(tree: Tree, opts: PrinterOptions = PrinterOptions()): String = {
    val ctx = PrinterContext(tree, Nil, opts.baseIndent, opts)
    printer.pp(tree)(using ctx)
    ctx.sb.toString
  }
}

trait Printer {
  protected val trees: Trees
  import trees._

  protected def optP(body: => Any)(using ctx: PrinterContext) = {
    if (requiresParentheses(ctx.current, ctx.parent)) {
      ctx.sb.append("(")
      body
      ctx.sb.append(")")
    } else {
      body
    }
  }

  private val dbquote = "\""
  private val notUC = "\u00AC"
  private val neqUC = "\u2260"
  private val notInUC = "\u2209"
  private val inUC = "\u2208"
  private val subsetUC = "\u2286"
  private val notSubsetUC = "\u2288"
  private val unionUC = "\u222A"
  private val interUC = "\u2229"
  private val forallUC = "\u2200"

  def pp(tree: Tree)(using ctx: PrinterContext): Unit = {
    if (requiresBraces(tree, ctx.parent) && !ctx.parent.contains(tree)) {
      p"""|{
          |  $tree
          |}"""
    } else {
      ppPrefix(tree)
      ppBody(tree)
      ppSuffix(tree)
    }
  }

  protected def ppPrefix(tree: Tree)(using ctx: PrinterContext): Unit = {
    if (ctx.opts.printTypes) {
      tree match {
        case t: Expr =>
          p"⟨"

        case _ =>
      }
    }
  }

  class BaseSort()
  case class FunType(args: Seq[Type], ret: Type)

  class Signature()
  //case class VarDecl() extends Signature
  case class FunDecl(id: Int, t: FunType, fd: FunDef) extends Signature:
    override def toString(): String = fd.id.toString + "_" + id
  case class UserFunDecl(fd: FunDef) extends Signature:
    override def toString(): String = fd.id.toString
  case class RetDecl(fd: FunDef) extends Signature:
    override def toString(): String = "ret_"+fd.id.toString

  case class Rule(tl: Term, tr: Term, c: Option[Formula]):
    override def toString(): String =
      val cString = c match
        case None => ""
        case Some(f) => " [" + f + "] "
      tl.toString + " -> " + tr.toString + cString + ";"


  sealed abstract class Formula
  case class FalseF() extends Formula:
    override def toString(): String = "false"

  case class TrueF() extends Formula:
    override def toString(): String = "true"

  case class VarF(id: Identifier) extends Formula:
    override def toString(): String = id.toString

  case class NotF(b: Formula) extends Formula:
    override def toString(): String = "not(" + b.toString + ")"


  class Term()

  sealed abstract class ArithExpr

  case class IntValueT(i: BigInt) extends ArithExpr:
    override def toString(): String = i.toString
  case class VarT(id: Identifier) extends ArithExpr:
    override def toString(): String = id.toString
  case class FunctionInvocationT(id: Identifier, args: Seq[ArithExpr]) extends ArithExpr:
    override def toString(): String = id.toString + "(" + args.mkString(", ") + ")"

  case class AddT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " + " + b.toString
  case class SubT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " - " + b.toString
  case class MulT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " * " + b.toString
  case class DivT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " / " + b.toString
  case class ModT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " mod " + b.toString
  case class AndT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " /\\ " + b.toString
  case class OrT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " \\/ " + b.toString
  case class GtT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " > " + b.toString
  case class LtT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " < " + b.toString
  case class LeT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " <= " + b.toString
  case class GeT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " >= " + b.toString
  case class EqT(a: ArithExpr, b: ArithExpr) extends ArithExpr:
    override def toString(): String = a.toString + " = " + b.toString
  case class NotT(a: ArithExpr) extends ArithExpr:
    override def toString(): String = "not(" + a.toString + ")"

  case class FalseT() extends ArithExpr:
    override def toString(): String = "false"

  case class TrueT() extends ArithExpr:
    override def toString(): String = "true"

  //case class ReturnT(id: Identifier, ret: ArithExpr) extends ArithExpr:
  //  override def toString(): String = "ret_"+id.name + "(" + ret.toString + ")"


  class Ret(id: Identifier, ret: Term) extends Term:
    override def toString(): String = "ret_"+id.name + "(" + ret.toString + ")"

  case class Eval(id: Int, fd: FunDef, t: Seq[Term]) extends Term:
    override def toString(): String = fd.id.toString + "_" + id + "(" + t.mkString(", ") + ")"

  class Expression() extends Term
  case class FunOrig(id: Identifier, arith_expr: Seq[ArithExpr]) extends Expression:
    override def toString(): String = id.toString + "(" + arith_expr.mkString(", ") + ")"
  case class ExprT(arith_expr: ArithExpr) extends Expression:
    override def toString(): String = arith_expr.toString

  protected def convert(f: FunDef, i: Int, x: Seq[Identifier], y: Seq[Identifier], S: Seq[Signature], R: Seq[Rule], Ss: Tree)(using ctx: PrinterContext): (Seq[Signature], Seq[Rule], Int) = {
    val tlb = FunOrig(f.id, x.map(VarT(_))++y.map(VarT(_))) // todo f's args instead of xy
    val trb = Eval(i, f, (x++y).map(e => ExprT(VarT(e))))


    val res = convert1(f, i, x, y, S, R, Ss)

    val S1 = res._1
    val R1 = res._2
    val i1 = res._3


    //1: find the term with id=i (last term)
    val tla1 = R1.filter(_.tr match{
      case Eval(id, _, _) => id == i1
      case a => println(a)
        false
      }).head.tr
    val fresh = VarT(new Identifier("fresh", 0, 0).freshen)
    //2: replace its return expression with  fresh variable
    val tla = tla1 match {
      case Eval(id, f, arith_expr) => Eval(id, f, arith_expr.init ++ Seq(ExprT(fresh)))
      case a => a }
    //3: right hand side is a return term (or error term)
    val tra = Ret(f.id, ExprT(fresh))

    val R2 = R1 ++ Seq(Rule(tlb, trb, None), Rule(tla, tra, None))
    val S2 = Seq(UserFunDecl(f), FunDecl(0, FunType(f.params.map(_.tpe), f.returnType), f)) ++ S1 ++ Seq(RetDecl(f))
    (S2, R2, i1)

  }

  // todo
  // merge boolean formula duplication

  protected def evalExp(e: Tree)(using ctx: PrinterContext): ArithExpr = {
    e match {
      case BooleanLiteral(true) => TrueT()
      case BooleanLiteral(false) => FalseT()
      case IntegerLiteral(v) => IntValueT(v)
      case Variable(id, _, _) => VarT(id)

      case And(List(a: Tree, b: Tree)) => AndT(evalExp(a), evalExp(b))
      case Or(List(a: Tree, b: Tree)) => OrT(evalExp(a), evalExp(b))
      case LessThan(a, b) => LtT(evalExp(a), evalExp(b))
      case GreaterThan(l, r) => GtT(evalExp(l), evalExp(r))
      case LessEquals(l, r) => LeT(evalExp(l), evalExp(r))
      case GreaterEquals(l, r) => GeT(evalExp(l), evalExp(r))
      case Equals(l, r) => EqT(evalExp(l), evalExp(r))
      case Not(a: Tree) => NotT(evalExp(a))

      case Plus(l, r) => AddT(evalExp(l), evalExp(r))
      case Minus(l, r) => SubT(evalExp(l), evalExp(r))
      case Times(l, r) => MulT(evalExp(l), evalExp(r))
      case Division(l, r) => DivT(evalExp(l), evalExp(r))
      case Remainder(l, r) => ???
      case Modulo(l, r) => ModT(evalExp(l), evalExp(r))


    }
  }

  protected def convert1(f: FunDef, i: Int, x: Seq[Identifier], y: Seq[Identifier], S: Seq[Signature], R: Seq[Rule], Ss: Tree)(using ctx: PrinterContext): (Seq[Signature], Seq[Rule], Int) = {
    val xy = x.map(VarT(_)) ++ y.map(VarT(_))
    val xy_terms = xy.map(ExprT(_))
    val x_terms = x.map(e => ExprT(VarT(e)))
    Ss match {
      case BooleanLiteral(_) | Variable(_, _, _) | IntegerLiteral(_) |
           And(_) | Or(_)| Not(_) |
           LessThan(_, _) | GreaterThan(_, _) | LessEquals(_, _) | GreaterEquals(_, _) | Equals(_, _) |
           Plus(_, _) | Minus(_, _) | Times(_, _) | Division(_, _) | Modulo(_, _) =>
        // todo finish
        val tl = Eval(i, f, xy_terms)
        val tr = Eval(i+1, f, xy_terms ++ Seq(ExprT(evalExp(Ss))))
        val R1 = R ++ Seq(Rule(tl, tr, None))
        val S1 = S ++ Seq(FunDecl(i+1, FunType(f.params.map(_.tpe), f.returnType), f))
        println(R1)
        (S1, R1, i+1)

      case Let(b, d, e) =>
        println("Let")
        //x.map((ctx.opts.symbols.get.sorts ++ ctx.opts.symbols.get.functions)(_))
        val convert_d = convert1(f, i, x, y, Seq(), Seq(), d)
        val S1 = S ++ convert_d._1
        val R1 = R ++ convert_d._2
        val j = convert_d._3
        convert1(f, j, x, y ++ Seq(b.id), S1, R1, e)

      case FunctionInvocation(g, tps, args) =>
        //val ep = args.map(e => convert1(f, i, x, y, S, R, e)) // todo update i each time
        val ep = args.map(e => evalExp(e))

        // to receive the fun call res.
        val r = VarT(new Identifier("fresh", 0, 0).freshen)

        val R2 = R ++ Seq(Rule(Eval(i, f, xy_terms), Eval(i+1, f, xy_terms ++ Seq(ExprT(FunctionInvocationT(g, args.map(e => evalExp(e)))))), None), Rule(Eval(i+1, f, xy_terms ++ Seq(Ret(g, ExprT(r)))), Eval(i+2, f, xy_terms ++ Seq(ExprT(r))), None))

        val S2 = S ++ Seq(FunDecl(i+1, FunType(f.params.map(_.tpe), f.returnType), f),
          FunDecl(i+2, FunType(f.params.map(_.tpe), f.returnType), f))
        (S2, R2, i+2)
      case IfExpr(e, ss, tt) =>
        println("If")
        val j = i
        val res2 = convert1(f, j+1, x++y, Seq(), Seq(), Seq(), ss)
        val S2 = res2._1
        val R2 = res2._2
        val k =  res2._3
        val res3 = convert1(f, k, x++y, Seq(), Seq(), Seq(), tt)
        val S3 = res3._1
        val R3 = res3._2
        val n =  res3._3

        val S2p = S2.filterNot(elem => elem match { case FunDecl(id, t, _) => id == k })
        val R2p = R2.map(elem => elem match {
          case Rule(tl, tr, c) =>
            tl match {
              case Eval(id, f, arith_expr) if id == k =>
                Rule(Eval(n, f, arith_expr), tr, c)
              case _ => elem
            }
            tr match {
              case Eval(id, f, arith_expr) if id == k =>
                Rule(tl, Eval(n, f, arith_expr), c)
              case _ => elem
            }
          case _ => elem
        })

        //convert1(f, n, x, y, Σ′, R′, Ss)

        // todo: this is code duplication? run convert1 for e even if there are no side effects ?
        val condition = e match {
          case BooleanLiteral(true) => TrueF()
          case BooleanLiteral(false) => FalseF()
          case Variable(id, _, _) => VarF(id) // todo
          case _ =>  FalseF() // todo
        }

        val Sp = S ++ S2p ++ S3 ++ Seq(FunDecl(j+1, FunType(f.params.map(_.tpe), f.returnType), f),
                             FunDecl(k, FunType(f.params.map(_.tpe), f.returnType), f))

        val Rp = R ++ R2p ++ R3 ++
        Seq(Rule(Eval(j, f, xy_terms) , Eval(j+1, f, xy_terms), Some(condition))) ++
        Seq(Rule(Eval(j, f, xy_terms) , Eval(k, f, xy_terms), Some(NotF(condition))))

        //println(Sp)
        //println(Rp)
        (Sp, Rp, n)
      case els =>
        println("not let")
        println(els)
        //println(Ss)
        (S, R, i+1)
    }

  }

  protected def ppBody(tree: Tree)(using ctx: PrinterContext): Unit = {
  //println("ppBody")
  tree match {
    case Variable(id, _, _) =>
      println("1")
      p"$id"

    case Let(vd, expr, SubString(v2: Variable, start, StringLength(v3: Variable))) if vd.toVariable == v2 && v2 == v3 =>
      println("2")
      p"$expr.substring($start)"

    case Let(b, d, e) =>
      println("3")
      p"""|val $b = $d
          |$e"""

    case Forall(args, e) =>
      println("4")
      ppForall(args, e)

    case Choose(res, pred) =>
      println("5")
      p"choose(($res) => $pred)"

    case Assume(pred, body) =>
      println("6")
      p"""|assume($pred)
          |$body"""

    case e @ ADT(id, tps, args) =>
      println("7")
      p"$id${nary(tps, ", ", "[", "]")}($args)"

    case And(exprs) => optP {
      p"${nary(exprs, " && ")}"
    }
    case Or(exprs) => optP {
      p"${nary(exprs, "| || ")}"
    } // Ugliness award! The first | is there to shield from stripMargin()
    case Not(Equals(l, r)) => optP {
      ppNeq(l, r)
    }
    case Implies(l, r) => optP {
      p"$l ==> $r"
    }
    case UMinus(expr) => p"-$expr"
    case Equals(l, r) => optP {
      p"$l == $r"
    }

    case StringConcat(lhs, rhs) => optP {
      p"$lhs + $rhs"
    }
    case SubString(expr, start, end) => p"$expr.substring($start, $end)"
    case StringLength(expr) => p"$expr.length"

    case Int8Literal(v) => p"$v"
    case Int16Literal(v) => p"$v"
    case Int32Literal(v) => p"$v"
    case Int64Literal(v) => p"$v"
    case BVLiteral(_, bits, size) => p"x${(size to 1 by -1).map(i => if (bits(i)) "1" else "0").mkString("")}"
    case IntegerLiteral(v) => p"$v"
    case FractionLiteral(n, d) =>
      if (d == 1) p"$n"
      else p"$n/$d"
    case CharLiteral(v) => p"'${StringEscapeUtils.escapeJava(v.toString)}'"
    case BooleanLiteral(v) => p"$v"
    case UnitLiteral() => p"()"
    case StringLiteral(v) =>
      if (v.count(c => c == '\n') >= 1 && v.length >= 80 && v.indexOf("\"\"\"") == -1) {
        p"$dbquote$dbquote$dbquote$v$dbquote$dbquote$dbquote"
      } else {
        val escaped = StringEscapeUtils.escapeJava(v)
        p"$dbquote$escaped$dbquote"
      }
    case GenericValue(tp, id) => p"$tp#$id"
    case Tuple(exprs) => p"($exprs)"
    case TupleSelect(t, i) => p"$t._$i"
    case IsConstructor(e, id) => p"$e is $id"
    case ADTSelector(e, id) => p"$e.$id"

    case FunctionInvocation(id, tps, args) =>
      println("8")
      p"$id${nary(tps, ", ", "[", "]")}"
      if (args.nonEmpty) {
        p"($args)"
      }

    case Application(caller, args) =>
      println("9")
      p"$caller($args)"

    case Lambda(Seq(vd), FunctionInvocation(id, Seq(), Seq(arg))) if vd.toVariable == arg =>
      p"$id"

    case Lambda(args, body) =>
      optP {
        p"($args) => $body"
      }

    case Plus(l, r) => optP {
      p"$l + $r"
    }
    case Minus(l, r) => optP {
      p"$l - $r"
    }
    case Times(l, r) => optP {
      p"$l * $r"
    }
    case Division(l, r) => optP {
      p"$l / $r"
    }
    case Remainder(l, r) => optP {
      p"$l % $r"
    }
    case Modulo(l, r) => optP {
      p"$l mod $r"
    }
    case LessThan(l, r) => optP {
      p"$l < $r"
    }
    case GreaterThan(l, r) => optP {
      p"$l > $r"
    }
    case LessEquals(l, r) => optP {
      p"$l <= $r"
    }
    case GreaterEquals(l, r) => optP {
      p"$l >= $r"
    }
    case BVNot(e) => optP {
      p"~$e"
    }
    case BVXor(l, r) => optP {
      p"$l ^ $r"
    }
    case BVOr(l, r) => optP {
      p"$l | $r"
    }
    case BVAnd(l, r) => optP {
      println("01")
      p"$l & $r"
    }
    case BVShiftLeft(l, r) => optP {
      p"$l << $r"
    }
    case BVAShiftRight(l, r) => optP {
      p"$l >> $r"
    }
    case BVLShiftRight(l, r) => optP {
      p"$l >>> $r"
    }

    case BVNarrowingCast(e, Int8Type())  => p"$e.toByte"
    case BVNarrowingCast(e, Int16Type()) => p"$e.toShort"
    case BVNarrowingCast(e, Int32Type()) => p"$e.toInt"
    case BVNarrowingCast(e, Int64Type()) => p"$e.toLong"
    case BVNarrowingCast(e, BVType(_, size)) => p"$e.toBV($size)"
    case BVWideningCast(e, Int8Type())  => p"$e.toByte"
    case BVWideningCast(e, Int16Type()) => p"$e.toShort"
    case BVWideningCast(e, Int32Type()) => p"$e.toInt"
    case BVWideningCast(e, Int64Type()) => p"$e.toLong"
    case BVWideningCast(e, BVType(_, size)) => p"$e.toBV($size)"
    case BVUnsignedToSigned(e) => p"$e.toSigned"
    case BVSignedToUnsigned(e) => p"$e.toUnsigned"

    case fs @ FiniteSet(rs, _) => p"{${rs}}"
    case fs @ FiniteBag(rs, _) => p"{${rs.toSeq}}"
    case fm @ FiniteMap(rs, dflt, _, _) =>
      if (rs.isEmpty) {
        p"{* -> $dflt}"
      } else {
        p"{${rs.toSeq}, * -> $dflt}"
      }
    case Not(ElementOfSet(e, s)) => ppNotIn(e, s)
    case ElementOfSet(e, s) => ppIn(e, s)
    case SubsetOf(l, r) => ppSubset(l, r)
    case Not(SubsetOf(l, r)) => ppNotSubset(l, r)
    case SetAdd(s, e) => ppSetAdd(s, e)
    case SetUnion(l, r) => ppSetUnion(l, r)
    case BagUnion(l, r) => ppSetUnion(l, r)
    case SetDifference(l, r) => p"$l \\ $r"
    case BagDifference(l, r) => p"$l \\ $r"
    case SetIntersection(l, r) => ppSetInter(l, r)
    case BagIntersection(l, r) => ppSetInter(l, r)
    case BagAdd(b, e) => p"$b + $e"
    case MultiplicityInBag(e, b) => p"$b($e)"
    case MapApply(m, k) => p"$m($k)"
    case MapUpdated(m, k, v) => p"$m.updated($k, $v)"
    case MapMerge(mask, m1, m2) => p"$mask.mapMerge($m1, $m2)"

    case Not(expr) => ppNot(expr)

    case vd @ ValDef(id, tpe, flags) =>
      if (flags.isEmpty) {
        p"$id: $tpe"
      } else {
        p"($id: $tpe)"
        for (f <- flags) p" @${f.asString(using ctx.opts)}"
      }

    case (tfd: TypedFunDef) => p"typed def ${tfd.id}[${tfd.tps}]"
    case (afd: TypedADTSort) => p"typed class ${afd.id}[${afd.tps}]"
    case (afd: TypedADTConstructor) => p"typed class ${afd.id}[${afd.tps}]"

    case tpd: TypeParameterDef =>
      p"${tpd.tp}"

    case TypeParameter(id, flags) =>
      p"$id"
      for (f <- flags) p" @${f.asString(using ctx.opts)}"

    case IfExpr(c, t, ie: IfExpr) =>
      optP {
        p"""|if ($c) {
            |  $t
            |} else $ie"""
      }

    case IfExpr(c, t, e) =>
      optP {
        p"""|if ($c) {
            |  $t
            |} else {
            |  $e
            |}"""
      }

    // Types
    case Untyped => p"<untyped>"
    case UnitType() => p"Unit"
    case Int8Type() => p"Byte"
    case Int16Type() => p"Short"
    case Int32Type() => p"Int"
    case Int64Type() => p"Long"
    case BVType(true, size) => p"Int$size"
    case BVType(false, size) => p"UInt$size"
    case IntegerType() => p"BigInt"
    case RealType() => p"Real"
    case CharType() => p"Char"
    case BooleanType() => p"Boolean"
    case StringType() => p"String"
    case SetType(bt) => p"Set[$bt]"
    case BagType(bt) => p"Bag[$bt]"
    case MapType(ft, tt) => p"Map[$ft, $tt]"
    case TupleType(tpes) => p"($tpes)"
    case FunctionType(fts, tt) => p"($fts) => $tt"
    case adt: ADTType =>
      p"${adt.id}${nary(adt.tps, ", ", "[", "]")}"

    case RefinementType(vd, pred) =>
      p"|{ $vd "
      ctx.sb.append("|")
      p"| $pred }"

    case PiType(params, to) => p"($params) => $to"
    case SigmaType(params, to) => p"($params, $to)"

    // Definitions
    case sort: ADTSort =>
      for (an <- sort.flags) p"""|@${an.asString(using ctx.opts)}
                                 |"""
      p"abstract class ${sort.id}"
      if (sort.tparams.nonEmpty) p"${nary(sort.tparams, ", ", "[", "]")}"
      for (cons <- sort.constructors) {
        p"""|
            |case class ${cons.id}"""
        if (sort.tparams.nonEmpty) p"${nary(sort.tparams, ", ", "[", "]")}"
        p"(${cons.fields})"
        p" extends ${sort.id}"
        if (sort.tparams.nonEmpty) p"${nary(sort.tparams.map(_.tp), ", ", "[", "]")}"
      }

    case cons: ADTConstructor =>
      val optTparams =
        ctx.opts.symbols.flatMap(_.lookupSort(cons.sort))
          .map(_.tparams).filter(_.nonEmpty)

      p"case class ${cons.id}"
      p"(${cons.fields})"
      optTparams.foreach(tparams => p"${nary(tparams, ", ", "[", "]")}")
      p" extends ${cons.sort}"
      optTparams.foreach(tparams => p"${nary(tparams.map(_.tp), ", ", "[", "]")}")

    case fd: FunDef =>
      println("fundef")
      //fd, 0 , f U (), (), (), ()
      val res = convert(fd, 0, Seq() ++ Seq(), fd.params.map(_.id), Seq(), Seq(), fd.fullBody)
      val s = "THEORY ints     ;\nLOGIC QF_LIA    ;\nSOLVER internal ;\n"+
        "SIGNATURE " + res._1.mkString(",") + " ;\n" + "RULES\n" + res._2.mkString("\n") +
        "\nQUERY termination"

       println(s)

       val fw = new java.io.FileWriter("example.ctrs");
       fw.write(s)
       fw.flush()
       fw.close()

      for (an <- fd.flags) {
        p"""|@${an.asString(using ctx.opts)}
            |"""
      }

      p"def ${fd.id}${nary(fd.tparams, ", ", "[", "]")}"
      if (fd.params.nonEmpty) {
        p"(${fd.params})"
      }

      p": ${fd.returnType} = "
      p"${fd.fullBody}"

    case _ => ctx.sb.append("Tree? (" + tree.getClass + ")")
  }}

  protected def ppSuffix(tree: Tree)(using ctx: PrinterContext): Unit = {
    if (ctx.opts.printTypes) {
      tree match {
        case t: Expr =>
          p" : ${t.getType(using ctx.opts.symbols.get)} ⟩"

        case _ =>
      }
    }
    if (ctx.opts.printPositions) {
      tree.getPos match {
        case op: OffsetPosition =>
          p"@($op)"
        case rp: RangePosition =>
          if (rp.lineFrom == rp.lineTo) {
            if (rp.colFrom == rp.colTo) {
              p"@(${rp.lineFrom}:${rp.colFrom})"
            } else {
              p"@(${rp.lineFrom}:${rp.colFrom}-${rp.colTo})"
            }
          } else {
            p"@(${rp.focusBegin}-${rp.focusEnd})"
          }
        case _ =>
          p"@(?)"
      }
    }
  }

  protected def isSimpleExpr(e: Expr): Boolean = e match {
    case _: Let => false
    case _: Assume => false
    case _ => true
  }

  protected def noBracesSub(e: Tree): Seq[Expr] = e match {
    case Let(_, _, bd) => Seq(bd)
    case IfExpr(_, t, e) => Seq(t, e) // if-else always has braces anyway
    case Assume(_, bd) => Seq(bd)
    case _ => Seq()
  }

  protected def requiresBraces(ex: Tree, within: Option[Tree]) = (ex, within) match {
    case (e: Expr, _) if isSimpleExpr(e) => false
    case (e: Expr, Some(within)) if noBracesSub(within) contains e => false
    case (e: Expr, Some(_)) => true
    case _ => false
  }

  protected def precedence(ex: Expr): Int = ex match {
    // 0: Letters
    case (_: ElementOfSet | _: Modulo) => 0
    // 1: |
    case (_: Or | _: BVOr) => 1
    // 2: ^
    case (_: BVXor) => 2
    // 3: &
    case (_: And | _: BVAnd | _: SetIntersection) => 3
    // 4: < >
    case (
      _: GreaterThan | _: GreaterEquals | _: LessEquals | _: LessThan |
      _: BVAShiftRight | _: BVLShiftRight | _: BVShiftLeft
      ) => 4
    // 5: = !
    case (_: Equals | _: Not | _: Implies) => 5
    // 6: :
    // 7: + -
    case (_: Plus | _: Minus | _: SetUnion | _: SetDifference | _: StringConcat) => 7
    // 8: * / %
    case (_: Times | _: Division | _: Remainder) => 8
    // 9: Other special characters
    case _ => 9
  }

  protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, None) => false
    case (_, Some(
      _: Definition | _: Let | _: IfExpr | _: ADT | _: Lambda | _: Choose | _: Tuple | _: Assume
    )) => false
    case (ex: StringConcat, Some(_: StringConcat)) => false
    case (_, Some(_: FunctionInvocation)) => false
    case (ie: IfExpr, _) => true
    case (e1: Expr, Some(e2: Expr)) if precedence(e1) > precedence(e2) => false
    case (_, _) => true
  }

  protected def ppNot(e: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$notUC$e"
    else p"!$e"

  protected def ppNeq(l: Tree, r: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$l $neqUC $r"
    else p"$l != $r"

  protected def ppNotIn(e: Tree, s: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$e $notInUC $s"
    else p"!$s.contains($e)"

  protected def ppIn(e: Tree, s: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$e $inUC $s"
    else p"$s.contains($e)"

  protected def ppSubset(l: Tree, r: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$l $subsetUC $r"
    else p"$l.subsetOf($r)"

  protected def ppNotSubset(l: Tree, r: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$l $notSubsetUC $r"
    else p"!$l.subsetOf($r)"

  protected def ppSetAdd(s: Tree, e: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$s $unionUC {$e}"
    else p"$s + $e"

  protected def ppSetUnion(l: Tree, r: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$l $unionUC $r"
    else p"$l ++ $r"

  protected def ppSetInter(l: Tree, r: Tree)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$l $interUC $r"
    else p"$l & $r"

  protected def ppForall(args: Seq[ValDef], e: Expr)(using pc: PrinterContext): Unit =
    if (pc.opts.printUnicode) p"$forallUC${nary(args)}. $e"
    else p"forall((${nary(args)}) => $e)"

  class PrintWrapper(val f: PrinterContext ?=> Any) {
    def print(ctx: PrinterContext) = f(using ctx)
  }

  extension (sc: StringContext) {
    def p(args: Any*)(using ctx: PrinterContext): Unit = {
      val sb = ctx.sb

      val strings = sc.parts.iterator
      val expressions = args.iterator

      var extraInd = 0
      var firstElem = true

      while (strings.hasNext) {
        val currval = strings.next()
        val s = if (currval != " || ") {
          currval.stripMargin
        } else currval

        // Compute indentation
        val start = s.lastIndexOf('\n')
        if (start >= 0 || firstElem) {
          var i = start + 1
          while (i < s.length && s(i) == ' ') {
            i += 1
          }
          extraInd = (i - start - 1) / 2
        }

        firstElem = false

        // Make sure new lines are also indented
        sb.append(s.replaceAll("\n", "\n" + ("  " * ctx.lvl)))

        val nctx = ctx.copy(lvl = ctx.lvl + extraInd)

        if (expressions.hasNext) {
          val e = expressions.next()

          e match {
            case (t1, t2) =>
              nary(Seq(t1, t2), " -> ").print(nctx)

            case ts: Seq[Any] =>
              nary(ts).print(nctx)

            case t: Tree =>
              // Don't add same tree twice in parents
              val parents = if (nctx.parents.headOption contains nctx.current) {
                nctx.parents
              } else {
                nctx.current :: nctx.parents
              }
              val nctx2 = nctx.copy(parents = parents, current = t)
              pp(t)(using nctx2)

            case id: Identifier =>
              val name = if (ctx.opts.printUniqueIds) {
                id.uniqueName
              } else {
                id.toString
              }
              p"$name"

            case p: PrintWrapper =>
              p.print(nctx)

            case e =>
              sb.append(e.toString)
          }
        }
      }
    }
  }

  def nary(ls: Seq[Any], sep: String = ", ", init: String = "", closing: String = ""): PrintWrapper = PrintWrapper {
    val (i, c) = if (ls.isEmpty) ("", "") else (init, closing)
    val strs = i +: List.fill(ls.size - 1)(sep) :+ c
    new StringContext(strs: _*).p(ls: _*)
  }

  def typed(t: Tree with Typed)(using Symbols): PrintWrapper = PrintWrapper {
    p"$t : ${t.getType}"
  }

  def typed(ts: Seq[Tree with Typed])(using Symbols): PrintWrapper = PrintWrapper {
    nary(ts.map(typed))
  }
}
