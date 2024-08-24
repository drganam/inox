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

  // TRS trees

  //class BaseSort()
  case class FunType(args: Seq[Type], ret: Type)

  sealed abstract class Signature
  //case class VarDecl() extends Signature

  case class FunDecl(id: Int, t: FunType, fd: FunDef) extends Signature // intermediate symbols (for Eval terms)
  case class UserFunDecl(fd: FunDef) extends Signature // user-defined (Scala) functions (for FunOrig terms)
  case class RetDecl(fd: FunDef) extends Signature // ret symbols -- one per user function (for Ret terms)

  sealed abstract class Term

  sealed abstract class ArithExpr
  case class IntValueT(i: BigInt) extends ArithExpr
  case class VarT(id: Identifier, t: Type) extends ArithExpr
  case class CallT(id: Identifier, args: Seq[ArithExpr]) extends ArithExpr
  case class AddT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class SubT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class MulT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class DivT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class ModT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class AndT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class OrT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class GtT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class LtT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class LeT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class GeT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class EqT(a: ArithExpr, b: ArithExpr) extends ArithExpr
  case class NotT(a: ArithExpr) extends ArithExpr
  case class FalseT() extends ArithExpr
  case class TrueT() extends ArithExpr
  case class ConsT(id: Identifier, v: List[ArithExpr]) extends ArithExpr

  protected def typeOfExpression(e: ArithExpr)(using ctx: PrinterContext): Type = e match
    case IntValueT(i: BigInt) => IntegerType()
    case VarT(id: Identifier, t: Type) => t
    case CallT(id: Identifier, args: Seq[ArithExpr]) => ctx.opts.symbols.get.functions(id).returnType
    case AddT(a: ArithExpr, b: ArithExpr) => IntegerType()
    case SubT(a: ArithExpr, b: ArithExpr) => IntegerType()
    case MulT(a: ArithExpr, b: ArithExpr) => IntegerType()
    case DivT(a: ArithExpr, b: ArithExpr) => IntegerType()
    case ModT(a: ArithExpr, b: ArithExpr) => IntegerType()
    case AndT(a: ArithExpr, b: ArithExpr) => BooleanType()
    case OrT(a: ArithExpr, b: ArithExpr) => BooleanType()
    case GtT(a: ArithExpr, b: ArithExpr) => BooleanType()
    case LtT(a: ArithExpr, b: ArithExpr) => BooleanType()
    case LeT(a: ArithExpr, b: ArithExpr) => BooleanType()
    case GeT(a: ArithExpr, b: ArithExpr) => BooleanType()
    case EqT(a: ArithExpr, b: ArithExpr) => BooleanType()
    case NotT(a: ArithExpr) => BooleanType()
    case FalseT() => BooleanType()
    case TrueT() => BooleanType()
    case ConsT(id: Identifier, v: List[ArithExpr]) => ADTType(id, v.map(typeOfExpression))


  case class Eval(id: Int, fd: FunDef, t: Seq[Term]) extends Term
  case class Ret(id: Identifier, ret: Term) extends Term
  sealed abstract class Expression extends Term
  case class FunOrig(id: Identifier, arith_expr: Seq[ArithExpr]) extends Expression
  case class ExprT(arith_expr: ArithExpr) extends Expression


  case class Rule(tl: Term, tr: Term, c: ArithExpr = TrueT()) // c is ArithExpr even though it must be of type Boolean


  // conversion
  // todo: x and y can be of Identifier type afterall?
  protected def convert(f: FunDef, i: Int, x: Seq[ArithExpr], y: Seq[ArithExpr], S: Seq[Signature], R: Seq[Rule], Ss: Expr)(using ctx: PrinterContext): (Seq[Signature], Seq[Rule], Int) = {
    val tlb = FunOrig(f.id, x++y) // todo f's args instead of xy
    val trb = Eval(i, f, (x++y).map(e => ExprT(e)))

    val SsTransformed = insertLets(shortCircuit(Ss))
    //println(SsTransformed)
    //val res = convert1(f, i, x, y, S, R, Ss)
    val res = convert1(f, i, x, y, S, R, SsTransformed)

    val S1 = res._1
    val R1 = res._2
    val i1 = res._3

    //1: find the term with id==i (the last term for f)
    val tla1 = R1.filter(_.tr match{
      case Eval(id, _, _) => id == i1
      case a =>
        println("SEE LINE 193")
        println(a)
        false
      }).head.tr

    val ret = VarT(new Identifier("ret", 0, 0).freshen, f.returnType)
    //2: replace its return expression with a fresh variable
    // todo: is this mandatory ?
    val tla = tla1 match {
      case Eval(id, f, arith_expr) => Eval(id, f, arith_expr.init ++ Seq(ExprT(ret)))
      case a => a }
    //3: right hand side is a ret term (or error term ?)
    val tra = Ret(f.id, ExprT(ret))

    val R2 = Seq(Rule(tlb, trb)) ++ R1 ++ Seq(Rule(tla, tra))
    val S2 = Seq(UserFunDecl(f), FunDecl(0, FunType(f.params.map(_.tpe), f.returnType), f)) ++ S1 ++ Seq(RetDecl(f))

    (S2, R2, i1)
  }


  protected def evalExp(e: Tree)(using ctx: PrinterContext): ArithExpr = e match
    case BooleanLiteral(true) => TrueT()
    case BooleanLiteral(false) => FalseT()
    case IntegerLiteral(v) => IntValueT(v)
    case Variable(id, t, _) => VarT(id, t)
    case FunctionInvocation(g, tps, args) => CallT(g, args.map(evalExp(_)))
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
    case ADTSelector(Variable(adt, _, _), selector) =>
      println("ADTSELECTOR") // keep a map to original selectors
      println(e)
      VarT(new Identifier(adt.uniqueName + selector.uniqueName, -1, 0), UnitType())
    // TODO nested selector a.b.c
    //case ADTSelector(ADTSelector(Variable(adt, _, _), selector1), selector2) =>
    //  println("nested selections")
    //  VarT(new Identifier(adt.uniqueName + selector1.uniqueName + selector2.uniqueName, -1, 0), UnitType())
    case ADT(id, tps, args) => ConsT(id, args.map(field => evalExp(field)).toList)
    case BVLiteral(s, v, n) => IntValueT(BVLiteral(s, v, n).toBigInt) // todo


  protected def convert1(f: FunDef, i: Int, x: Seq[ArithExpr], y: Seq[ArithExpr], S: Seq[Signature], R: Seq[Rule], Ss: Tree, pathc: ArithExpr = TrueT())(using ctx: PrinterContext): (Seq[Signature], Seq[Rule], Int) = {
    val xy = x++y//x.map(v => VarT(v._1, v._2)) ++ y.map(v => VarT(v._1, v._2))
    val xy_terms = xy.map(ExprT(_))
    //x.map((ctx.opts.symbols.get.sorts ++ ctx.opts.symbols.get.functions)(_))
    Ss match {
      case BooleanLiteral(_) | And(_) | Or(_)| Not(_) | Equals(_, _) |
           LessThan(_, _) | GreaterThan(_, _) | LessEquals(_, _) | GreaterEquals(_, _)  =>
        val tl = Eval(i, f, xy_terms)
        val tr = Eval(i+1, f, xy_terms ++ Seq(ExprT(evalExp(Ss))))
        val R1 = R ++ Seq(Rule(tl, tr, pathc))
        val S1 = S ++ Seq(FunDecl(i+1, FunType(xy.map(typeOfExpression) ++ Seq(BooleanType()), f.returnType), f))
        (S1, R1, i+1)
      case IntegerLiteral(_) | Plus(_, _) | Minus(_, _) | Times(_, _) | Division(_, _) | Modulo(_, _) =>
        val tl = Eval(i, f, xy_terms)
        val tr = Eval(i+1, f, xy_terms ++ Seq(ExprT(evalExp(Ss))))
        val R1 = R ++ Seq(Rule(tl, tr, pathc))
        val S1 = S ++ Seq(FunDecl(i+1, FunType(xy.map(typeOfExpression) ++ Seq(IntegerType()), f.returnType), f))
        (S1, R1, i+1)
      case Variable(_, t, _) =>
        val tl = Eval(i, f, xy_terms)
        val tr = Eval(i+1, f, xy_terms ++ Seq(ExprT(evalExp(Ss))))
        val R1 = R ++ Seq(Rule(tl, tr, pathc))
        val S1 = S ++ Seq(FunDecl(i+1, FunType(xy.map(typeOfExpression) ++ Seq(t), f.returnType), f))
        (S1, R1, i+1)
      case s @ ADTSelector(adt, selector) =>
        val cons = s.constructor(using ctx.opts.symbols.get)
        val fields = cons.fields

        val freshid = adt match {
          case Variable(id, _, _ ) => id.uniqueName
          case _ => ""
        }

        val fresh_fields = fields.map(v =>
          Variable(new Identifier(freshid + v.id.uniqueName, -1, 0), v.tpe, List()))

        val search = evalExp(adt)

        // in xy terms
        // find adt, which is of var type
        // replace it with cons(fields)
        val xy_terms_adt = xy_terms.map(elem => elem match
          case ExprT(s) if s == search =>
            ExprT(ConsT(cons.id, fresh_fields.map(fresh => VarT(fresh.id, fresh.tpe)).toList))
          case _ => elem
        )

        val tl = Eval(i, f, xy_terms_adt)
        val tr = Eval(i+1, f, xy_terms ++ Seq(ExprT(evalExp(Ss))))
        val R1 = R ++ Seq(Rule(tl, tr, pathc))
        // todo update Seq(UnitType())
        val S1 = S ++ Seq(FunDecl(i+1, FunType(xy.map(typeOfExpression) ++ Seq(UnitType()), f.returnType), f))
        (S1, R1, i+1)

      case ADT(id, _, _) =>
        val tl = Eval(i, f, xy_terms)
        val tr = Eval(i+1, f, xy_terms ++ Seq(ExprT(evalExp(Ss))))
        val R1 = R ++ Seq(Rule(tl, tr, pathc))
        // todo update Seq(UnitType())
        val S1 = S ++ Seq(FunDecl(i+1, FunType(xy.map(typeOfExpression) ++ Seq(UnitType()), f.returnType), f))
        (S1, R1, i+1)

      // useless info ?
      case Assume(IsConstructor(_, _), body) =>
        println("assume")
        convert1(f, i, x, y, S, R, body, pathc)

      case Assume(pred, body) =>
        println("assume")
        println(pred)
        convert1(f, i, x, y, S, R, body, if (pathc == TrueT()) evalExp(pred) else AndT(evalExp(pred), pathc))

      case Let(b, d, e) =>
        val convert_d = convert1(f, i, x, y, Seq(), Seq(), d, pathc)
        val S1 = convert_d._1
        val R1 = convert_d._2
        val j = convert_d._3

        // todo refactor this trimming because it's used for every block
        val R1p = R1.map(elem => elem match {
          case Rule(tl, tr, c) =>
            tr match {
              case Eval(id, f, arith_expr) if id == j =>
                val t = arith_expr.take((x++y).size) ++ Seq(arith_expr.last)
                Rule(tl, Eval(id, f, t), c)
              case _ => elem
            }
          })

        val S1p = S1.map(elem => elem match
          case FunDecl(id, t, fun) if id == j =>
            FunDecl(id, FunType(t.args.take((x++y).size) ++ Seq(t.args.last), t.ret),fun)
          case _ => elem
        )

        val S2 = S ++ S1p
        val R2 = R ++ R1p

        convert1(f, j, x, y ++ Seq(VarT(b.id, b.tpe)), S2, R2, e, pathc)

      case FunctionInvocation(g, tps, args) =>
        val retTpe = ctx.opts.symbols.get.functions(g).returnType
        val ret = VarT(new Identifier("fresh", 0, 0).freshen, retTpe) // to receive the fun call result

        val R2 = R ++ Seq(
          Rule(Eval(i, f, xy_terms), Eval(i+1, f, xy_terms ++ Seq(ExprT(CallT(g, args.map(e => evalExp(e)))))), pathc),
          Rule(Eval(i+1, f, xy_terms ++ Seq(Ret(g, ExprT(ret)))), Eval(i+2, f, xy_terms ++ Seq(ExprT(ret))), pathc))

        val S2 = S ++ Seq(
          FunDecl(i+1, FunType(xy.map(typeOfExpression) ++ Seq(retTpe), f.returnType), f),
          FunDecl(i+2, FunType(xy.map(typeOfExpression) ++ Seq(retTpe), f.returnType), f))

        (S2, R2, i+2)

      case IfExpr(IsConstructor(e, id), ss, tt) =>
        println("adt matching")

        val s = ctx.opts.symbols.get
        val cons = s.lookupConstructor(id)
        val constructors = cons.get.getSort(using s).constructors


        val freshid = e match {
          case Variable(id, _, _ ) => id.uniqueName
          case _ => ""
        }

        val fresh_fields = cons.get.fields.map(v =>
          Variable(new Identifier(freshid + v.id.uniqueName, -1, 0), v.tpe, List()))

        val search = evalExp(e)

        // in xy terms
        // find e, which is of base type
        // replace it with id(fields), which is of matched type
        val xy_terms_case = xy_terms.map(elem => elem match
          case ExprT(s) if s == search =>
            ExprT(ConsT(id, fresh_fields.map(fresh => VarT(fresh.id, fresh.tpe)).toList))
            //ExprT(ConsT(id, cons.get.fields.map(field => VarT(field.id, field.tpe)).toList))
          case _ => elem
        )

        val nnn = xy_terms_case.map(elem =>
          elem match
            case ExprT(e) => e
        )

        val j = i
        // convert then branch:
        // todo: R2 should have A(a1, a2) in xy_terms_case and not just generic scrut$2
        // todo: in x++y, replace scrut$2 with e.g. A(v$41)
        val res2 = convert1(f, j+1, nnn, Seq(), Seq(), Seq(), ss, pathc)
        val S2 = res2._1
        val R2 = res2._2
        val k =  res2._3
        // convert else branch:
        val res3 = convert1(f, k, x++y, Seq(), Seq(), Seq(), tt, pathc)
        val S3 = res3._1
        val R3 = res3._2
        val n =  res3._3

        // in R3
        // replace fj+1 with fj
        //val R3p = R3
        val R3p = R3.map(elem => elem match {
          case Rule(tl, tr, c) =>
            tl match {
              case Eval(id, f, arith_expr) if id == j+1 =>
                Rule(Eval(j, f, arith_expr), tr, c)
              case _ => elem
            }
        })
        val S2p = S2
        val S3p = S3


        val R2p = R2.map(elem => elem match {
          case Rule(tl, tr, c) =>
            tl match {
              case Eval(id, f, arith_expr) if id == k =>
                val t = arith_expr.take((x++y).size) ++ Seq(arith_expr.last)
                Rule(Eval(n, f, t), tr, c)
              case _ => elem
            }
            tr match {
              case Eval(id, f, arith_expr) if id == k =>
                val t = arith_expr.take((x++y).size) ++ Seq(arith_expr.last)
                Rule(tl, Eval(n, f, t), c)
              case _ => elem
            }
        })

        val Sp = S ++ Seq(
                FunDecl(j+1, FunType(xy.map(typeOfExpression), f.returnType), f),
                FunDecl(k, FunType(xy.map(typeOfExpression), f.returnType), f)) ++
                S2p ++ S3p





        val xy_terms_case_not = constructors.filterNot(_ == cons.get).map(c =>
          val fresh_fields = c.fields.map(v => Variable(new Identifier(freshid + v.id.uniqueName, -1, 0), v.tpe, List()))
          xy_terms.map(elem => elem match
          case ExprT(s) if s == search =>
            ExprT(ConsT(c.id, fresh_fields.map(fresh => VarT(fresh.id, fresh.tpe)).toList))
            //ExprT(ConsT(c.id, c.fields.map(field => VarT(field.id, field.tpe)).toList))
          case _ => elem
        ))

        val Rp = R ++
                Seq(Rule(Eval(j, f, xy_terms_case) , Eval(j+1, f, xy_terms_case), pathc)) ++ // if IsConstructor(e, id)
                xy_terms_case_not.map(t => Rule(Eval(j, f, t) , Eval(k, f, t), pathc)) ++ // if IsNotConstructor(e, id)
                R2p ++ R3p
        (Sp, Rp, n)

      case IfExpr(e, ss, tt) =>
        val j = i
        val condition = evalExp(e)

        // convert then branch:
        val res2 = convert1(f, j+1, x++y, Seq(), Seq(), Seq(), ss, if (pathc == TrueT()) condition else AndT(condition, pathc))
        val S2 = res2._1
        val R2 = res2._2
        val k =  res2._3
        //convert else branch:
        val res3 = convert1(f, k, x++y, Seq(), Seq(), Seq(), tt, if (pathc == TrueT()) NotT(condition) else AndT(NotT(condition), pathc))
        val S3 = res3._1
        val R3 = res3._2
        val n =  res3._3

        // two adjustments for fk and fn:
        // 1: skip the else branch in numbering - fk becomes fn
        // 2: remove what's out of scope outside of then/else branches:
        //        in Rk, keep only the first |xy| params plus the last one (ret)
        //        in Rn, keep only the first |xy| params plus the last one (ret)

        val R2p = R2.map(elem => elem match {
          case Rule(tl, tr, c) =>
            tl match {
              case Eval(id, f, arith_expr) if id == k =>
                val t = arith_expr.take((x++y).size) ++ Seq(arith_expr.last)
                Rule(Eval(n, f, t), tr, c)
              case _ => elem
            }
            tr match {
              case Eval(id, f, arith_expr) if id == k =>
                val t = arith_expr.take((x++y).size) ++ Seq(arith_expr.last)
                Rule(tl, Eval(n, f, t), c)
              case _ => elem
            }
        })

        val R3p = R3.map(elem => elem match {
          case Rule(tl, tr, c) =>
            tl match {
              case Eval(id, f, arith_expr) if id == n =>
                val t = arith_expr.take((x++y).size) ++ Seq(arith_expr.last)
                Rule(Eval(n, f, t), tr, c)
              case _ => elem
            }
            tr match {
              case Eval(id, f, arith_expr) if id == n =>
                val t = arith_expr.take((x++y).size) ++ Seq(arith_expr.last)
                Rule(tl, Eval(n, f, t), c)
              case _ => elem
            }
        })

        val S2p = S2.filterNot(elem => elem match
          case FunDecl(id, t, _) => id == k
          case _ => false
        )

        val S3p = S3.map(elem => elem match
          case FunDecl(id, t, fun) if id == n =>
            FunDecl(id, FunType(t.args.take((x++y).size) ++ Seq(t.args.last), t.ret),fun)
          case _ => elem
        )


        val Sp = S ++ Seq(
                FunDecl(j+1, FunType(xy.map(typeOfExpression), f.returnType), f),
                FunDecl(k, FunType(xy.map(typeOfExpression), f.returnType), f)) ++
                S2p ++ S3p

        val Rp = R ++
                Seq(Rule(Eval(j, f, xy_terms) , Eval(j+1, f, xy_terms), if (pathc == TrueT()) condition else AndT(condition, pathc))) ++
                Seq(Rule(Eval(j, f, xy_terms) , Eval(k, f, xy_terms), if (pathc == TrueT()) NotT(condition) else AndT(NotT(condition), pathc))) ++
                R2p ++ R3p

        (Sp, Rp, n)

      case Choose(res, pred) =>
        //val fresh = Variable(new Identifier("v", 0, 0).freshen, res.getType(using ctx.opts.symbols.get), List())
        //convert1(f, i, x, y, S, R, fresh, if (pathc == TrueT()) evalExp(pred) else AndT(evalExp(pred), pathc))
        (S, R, i) // noop

      case els =>
        println("new case")
        println(els)
        (S, R, i)
    }

  }


  // printers for CTRL and APROVE

  protected def printCTRL(ctrs: (Seq[Signature], Seq[Rule]))(using ctx: PrinterContext): String =
    "THEORY ints     ;\nLOGIC QF_LIA    ;\nSOLVER internal ;\n"+
    "SIGNATURE\n" + ctrs._1.map(printCTRL(_)).mkString(" ;\n") + " ;\n" +
    "RULES\n" + ctrs._2.map(printCTRL(_)).mkString("\n") +
    "\nQUERY termination"

  // todo: allow print without types as well
  protected def printCTRL(s: Signature): String = s match
    case FunDecl(id, t, fd) =>
      fd.id.uniqueName + "_" + id + " : " +
      t.args.map(printCTRL(_)).mkString(" * ") +
      " => " + printCTRL(fd.returnType)
    case UserFunDecl(fd) =>
      fd.id.uniqueName + " : " +
      fd.params.map(_.tpe).map(printCTRL(_)).mkString(" * ") +
      " => " + printCTRL(fd.returnType)
    case RetDecl(fd) =>
      "ret_" + fd.id.uniqueName + " : " +
      printCTRL(fd.returnType) +
      " => " + printCTRL(fd.returnType)

  protected def printCTRL(r: Rule)(using ctx: PrinterContext): String =
    val cString = r.c match
      case TrueT() => ""
      case f => " [" + printCTRL(f) + "] "
    printCTRL(r.tl) + " -> " + printCTRL(r.tr) + cString + ";"

  protected def printCTRL(t: Term)(using ctx: PrinterContext): String = t match
    case Ret(id, ret) =>
      "ret_" + id.uniqueName + "(" + printCTRL(ret) + ")"
    case Eval(id: Int, fd: FunDef, t: Seq[Term]) =>
      fd.id.uniqueName + "_" + id + "(" + t.map(printCTRL(_)).mkString(", ") + ")"
    case FunOrig(id: Identifier, arith_expr: Seq[ArithExpr]) =>
      id.uniqueName + "(" + arith_expr.map(printCTRL(_)).mkString(", ") + ")"
    case ExprT(arith_expr) =>
      printCTRL(arith_expr)

  protected def printCTRL(e: ArithExpr)(using ctx: PrinterContext): String = e match
    case IntValueT(i: BigInt) =>
      i.toString
    case VarT(id: Identifier, t: Type) =>
      ctx.opts.symbols.get.lookupConstructor(id) match
        case None => id.uniqueName
        case Some(c) => id.uniqueName + "(" + c.fields.map(field => VarT(field.id, field.tpe)).map(printCTRL(_)).mkString(", ") + ")"
    case AddT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " + " + printCTRL(b)
    case SubT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " - " + printCTRL(b)
    case MulT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " * " + printCTRL(b)
    case DivT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " / " + printCTRL(b)
    case ModT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " mod " + printCTRL(b)
    case AndT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " /\\ " + printCTRL(b)
    case OrT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " \\/ " + printCTRL(b)
    case GtT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " > " + printCTRL(b)
    case LtT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " < " + printCTRL(b)
    case LeT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " <= " + printCTRL(b)
    case GeT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " >= " + printCTRL(b)
    case EqT(a: ArithExpr, b: ArithExpr) =>
      printCTRL(a) + " = " + printCTRL(b)
    case NotT(a: ArithExpr) =>
      "not(" + printCTRL(a) + ")"
    case CallT(id: Identifier, args: Seq[ArithExpr]) =>
      id.uniqueName + "(" + args.map(printCTRL(_)).mkString(", ") + ")"
    case FalseT() =>
      "false"
    case TrueT() =>
      "true"
    case ConsT(id: Identifier, v: List[ArithExpr]) =>
      val f = ctx.opts.symbols.get.lookupConstructor(id).get.fields
      val fields = f.map(field => VarT(field.id, field.tpe))
      id.uniqueName + "(" + fields.map(printCTRL(_)).mkString(", ") + ")"

  protected def printCTRL(t: Type): String = t match
    case BooleanType() => "Bool"
    case IntegerType() => "Int"
    case _ => t.toString

  protected def printAPROVE(ctrs: (Seq[Signature], Seq[Rule]))(using ctx: PrinterContext): String =
    "(VAR " + printAPROVE(ctrs._2).distinct.mkString(" ") + ")\n" +
    "(RULES\n" + ctrs._2.map(printAPROVE(_)).mkString("\n") + "\n)"

  protected def printAPROVE(r: Rule)(using ctx: PrinterContext): String =
    val cString = r.c match
      case TrueT() => ""
      case f => " :|: " + printAPROVE(f)
    printAPROVE(r.tl) + " -> " + printAPROVE(r.tr) + cString

  // TODO finish -- prints vars from all the rules
  protected def printAPROVE(r: Seq[Rule])(using ctx: PrinterContext): List[String] =
    val t = r.map(e => List(e.tr, e.tl)).flatten
    t.toList.flatMap(ter => ter match
      case Ret(id, ret) =>
        List() //"ret_" + id.name + "(" + printAPROVE(ret) + ")"
      case Eval(id, fd, t) =>
        t.flatMap(e => e match
          case ExprT(VarT(id, _)) =>
            ctx.opts.symbols.get.lookupConstructor(id) match
            case None =>
              List(id)
            case Some(c) =>
              List(id) ++ c.fields.map(field => field.id)
          case ExprT(ConsT(id, v)) =>
            v.flatMap(f => f match
              case VarT(id, _) => Some(id)
              case _ => None
            )
          case _ => List()
        ).toList.map(_.uniqueName)
      case FunOrig(id: Identifier, arith_expr: Seq[ArithExpr]) =>
        List() //id.uniqueName + "(" + arith_expr.map(printAPROVE(_)).mkString(", ") + ")"
      case ExprT(arith_expr) =>
        List() //printAPROVE(arith_expr)
    )

  protected def printAPROVE(t: Term)(using ctx: PrinterContext): String = t match
    case Ret(id, ret) =>
      "ret_" + id.name + "(" + printAPROVE(ret) + ")"
    case Eval(id: Int, fd: FunDef, t: Seq[Term]) =>
      fd.id.uniqueName + "_" + id  + "(" + t.map(printAPROVE(_)).mkString(", ") + ")"
    case FunOrig(id: Identifier, arith_expr: Seq[ArithExpr]) =>
      id.uniqueName + "(" + arith_expr.map(printAPROVE(_)).mkString(", ") + ")"
    case ExprT(arith_expr) =>
      printAPROVE(arith_expr)

  protected def printAPROVE(e: ArithExpr)(using ctx: PrinterContext): String = e match
    case IntValueT(i: BigInt) =>
      i.toString
    case VarT(id: Identifier, t: Type) =>
      ctx.opts.symbols.get.lookupConstructor(id) match
        case None =>
          id.uniqueName
        case Some(c) =>
          id.uniqueName + "(" + c.fields.map(field => VarT(field.id, field.tpe)).map(printCTRL(_)).mkString(", ") + ")"
    case AddT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " + " + printAPROVE(b)
    case SubT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " - " + printAPROVE(b)
    case MulT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " * " + printAPROVE(b)
    case DivT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " / " + printAPROVE(b)
    case ModT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " % " + printAPROVE(b)
    case AndT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " /\\ " + printAPROVE(b)
    case OrT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " \\/ " + printAPROVE(b)
    case GtT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " > " + printAPROVE(b)
    case LtT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " < " + printAPROVE(b)
    case LeT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " <= " + printAPROVE(b)
    case GeT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " >= " + printAPROVE(b)
    case EqT(a: ArithExpr, b: ArithExpr) =>
      printAPROVE(a) + " = " + printAPROVE(b)
    case NotT(a: ArithExpr) =>
      "!" + printAPROVE(a)
    case CallT(id: Identifier, args: Seq[ArithExpr]) =>
      id.uniqueName + "(" + args.map(printAPROVE(_)).mkString(", ") + ")"
    case FalseT() =>
      "false"
    case TrueT() =>
      "true"
    case ConsT(id: Identifier, v: List[ArithExpr]) =>
      // val f = ctx.opts.symbols.get.lookupConstructor(id).get.fields
      // val fields = f.map(field => VarT(field.id, field.tpe))
      // println("fields")
      // println(fields.map(printCTRL(_)).mkString(", "))
      // id.uniqueName + "(" + fields.map(printCTRL(_)).mkString(", ") + ")"
      id.uniqueName + "(" + v.map(printCTRL(_)).mkString(", ") + ")"


  protected def printCORA(ctrs: (Seq[Signature], Seq[Rule])): String =
    "THEORY ints     ;\nLOGIC QF_LIA    ;\nSOLVER internal ;\n"+
    "SIGNATURE " + ctrs._1.map(printCORA(_)).mkString(" ;\n") + " ;\n" +
    "RULES\n" + ctrs._2.map(printCORA(_)).mkString("\n") +
    "\nQUERY termination"

  // todo: allow print without types as well
  protected def printCORA(s: Signature): String = s match
    case FunDecl(id, t, fd) =>
      fd.id.uniqueName + "_" + id + " : " +
      t.args.map(printCORA(_)).mkString(" * ") +
      " => " + printCORA(fd.returnType)
    case UserFunDecl(fd) =>
      fd.id.uniqueName + " : " +
      fd.params.map(_.tpe).map(printCORA(_)).mkString(" * ") +
      " => " + printCORA(fd.returnType)
    case RetDecl(fd) =>
      "ret_" + fd.id.uniqueName + " : " +
      printCORA(fd.returnType) +
      " => " + printCORA(fd.returnType)

  protected def printCORA(r: Rule): String =
    val cString = r.c match
      case TrueT() => ""
      case f => " | " + printCORA(f)
    printCORA(r.tl) + " -> " + printCORA(r.tr) + cString + ";"

  protected def printCORA(t: Term): String = t match
    case Ret(id, ret) =>
      "ret_" + id.uniqueName + "(" + printCORA(ret) + ")"
    case Eval(id: Int, fd: FunDef, t: Seq[Term]) =>
      fd.id.uniqueName + "_" + id + "(" + t.map(printCORA(_)).mkString(", ") + ")"
    case FunOrig(id: Identifier, arith_expr: Seq[ArithExpr]) =>
      id.uniqueName + "(" + arith_expr.map(printCORA(_)).mkString(", ") + ")"
    case ExprT(arith_expr) =>
      printCORA(arith_expr)

  protected def printCORA(e: ArithExpr): String = e match
    case IntValueT(i: BigInt) =>
      i.toString
    case VarT(id: Identifier, t: Type) =>
      id.uniqueName
    case AddT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " + " + printCORA(b)
    case SubT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " - " + printCORA(b)
    case MulT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " * " + printCORA(b)
    case DivT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " / " + printCORA(b)
    case ModT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " mod " + printCORA(b)
    case AndT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " /\\ " + printCORA(b)
    case OrT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " \\/ " + printCORA(b)
    case GtT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " > " + printCORA(b)
    case LtT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " < " + printCORA(b)
    case LeT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " <= " + printCORA(b)
    case GeT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " >= " + printCORA(b)
    case EqT(a: ArithExpr, b: ArithExpr) =>
      printCORA(a) + " = " + printCORA(b)
    case NotT(a: ArithExpr) =>
      "not(" + printCORA(a) + ")"
    case CallT(id: Identifier, args: Seq[ArithExpr]) =>
      id.uniqueName + "(" + args.map(printCORA(_)).mkString(", ") + ")"
    case FalseT() =>
      "false"
    case TrueT() =>
      "true"
    case ConsT(id: Identifier, v: List[ArithExpr]) =>
      id.uniqueName + "(" + v.map(printCORA(_)).mkString(", ") + ")"

  protected def printCORA(t: Type): String = t match
    case BooleanType() => "Bool"
    case IntegerType() => "Int"
    case _ => t.toString


    // a && b
    // if (a) b else false
    // a || b
    // if (a) true else b

  protected def shortCircuit(t: Expr): Expr =
    t match
      case And(Seq(a: Expr, b: Expr)) => // TODO special case, check the next and remove this if ok
        IfExpr(shortCircuit(a), shortCircuit(b), BooleanLiteral(false))
      case And(l) =>
        def chain(l: List[Expr]): Expr = l match
          case x::Nil =>
            shortCircuit(x)
          case x::xs =>
            IfExpr(shortCircuit(x), chain(xs), BooleanLiteral(false))
          case Nil =>
            t
        chain(l.toList)
      case Or(Seq(a: Expr, b: Expr)) =>
        IfExpr(shortCircuit(a), BooleanLiteral(true), shortCircuit(b))
      case Or(l) =>
        def chain(l: List[Expr]): Expr = l match
          case x::Nil =>
            shortCircuit(x)
          case x::xs =>
            IfExpr(shortCircuit(x), BooleanLiteral(true), chain(xs))
          case Nil =>
            t
        chain(l.toList)
      case Let(b, d, e) =>
        Let(b, shortCircuit(d), shortCircuit(e))
      case IfExpr(e, ss, tt) =>
        IfExpr(shortCircuit(e), shortCircuit(ss), shortCircuit(tt))
      case FunctionInvocation(g, tps, args) =>
        FunctionInvocation(g, tps, args.map(shortCircuit(_)))
      case BooleanLiteral(_) => t
      case IntegerLiteral(_) => t
      case Variable(_, _, _) => t
      case LessThan(a, b) => LessThan(shortCircuit(a), shortCircuit(b))
      case GreaterThan(l, r) => GreaterThan(shortCircuit(l), shortCircuit(r))
      case LessEquals(l, r) => LessEquals(shortCircuit(l), shortCircuit(r))
      case GreaterEquals(l, r) => GreaterEquals(shortCircuit(l), shortCircuit(r))
      case Equals(l, r) => Equals(shortCircuit(l), shortCircuit(r))
      case Not(a: Tree) => Not(shortCircuit(a))
      case Plus(l, r) => Plus(shortCircuit(l), shortCircuit(r))
      case Minus(l, r) => Minus(shortCircuit(l), shortCircuit(r))
      case Times(l, r) => Times(shortCircuit(l), shortCircuit(r))
      case Division(l, r) => Division(shortCircuit(l), shortCircuit(r))
      case Remainder(l, r) => Modulo(shortCircuit(l), shortCircuit(r)) // ???
      case Modulo(l, r) => Modulo(shortCircuit(l), shortCircuit(r))
      case Choose(res, pred) =>
        println("choose")
        Choose(res, shortCircuit(pred))
      case IsConstructor(e, id) => IsConstructor(shortCircuit(e), id)
      case ADTSelector(adt, selector) => ADTSelector(shortCircuit(adt), selector)
      case Assume(pred, body) => Assume(pred, shortCircuit(body))
      case ADT(id, tps, args) => ADT(id, tps, args.map(shortCircuit))
      case _ =>
        println("default")
        println(t)
        t

  // lets for fun. call args etc.
  // todo refactor
  protected def insertLets(t: Expr)(using ctx: PrinterContext): Expr = t match
    case And(Seq(a: Expr, b: Expr)) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, BooleanType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, BooleanType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), And(Seq(freshA, freshB))))
    case Or(Seq(a: Expr, b: Expr)) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, BooleanType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, BooleanType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), Or(Seq(freshA, freshB))))
    case Let(b, d, e) =>
      Let(b, insertLets(d), insertLets(e))
    case IfExpr(v @ Variable(_, _, _), ss, tt) =>
      IfExpr(v, insertLets(ss), insertLets(tt))
    case IfExpr(IsConstructor(e, id), ss, tt) =>
      IfExpr(IsConstructor(insertLets(e), id), insertLets(ss), insertLets(tt))
    case IfExpr(e, ss, tt) =>
      val fresh = Variable(new Identifier("tmp", 0, 0).freshen, e.getType(using ctx.opts.symbols.get), List())
      Let(fresh.toVal, insertLets(e), IfExpr(fresh, insertLets(ss), insertLets(tt)))
      // IfExpr(insertLets(e), insertLets(ss), insertLets(tt))
    case FunctionInvocation(g, tps, args) =>
      def chain(l: Seq[Expr], freshs: List[Variable]): Expr = l match
        case(Variable(id, t, l) :: Nil) => FunctionInvocation(g, tps, freshs++List(Variable(id, t, l)))
        case x::Nil =>
          val freshA = Variable(new Identifier("tmp", 0, 0).freshen, x.getType(using ctx.opts.symbols.get), List())
          Let(freshA.toVal, insertLets(x), FunctionInvocation(g, tps, freshs++List(freshA)))
        case(Variable(id, t, l) :: xs) => chain(xs, freshs++List(Variable(id, t, l)))
        case(x::xs) =>
          val freshA = Variable(new Identifier("tmp", 0, 0).freshen, x.getType(using ctx.opts.symbols.get), List())
          Let(freshA.toVal, insertLets(x), chain(xs, freshs++List(freshA)))
      if (args.isEmpty) FunctionInvocation(g, tps, args)
      else chain(args, List())
    case BooleanLiteral(_) => t
    case IntegerLiteral(_) => t
    case Variable(_, _, _) => t
    case LessThan(a: Variable, b: Variable) => t
    case LessThan(a: IntegerLiteral, b: IntegerLiteral) => t
    case LessThan(a: IntegerLiteral, b: Variable) => t
    case LessThan(a: Variable, b: IntegerLiteral) => t
    case GreaterThan(a: Variable, b: Variable) => t
    case GreaterThan(a: IntegerLiteral, b: IntegerLiteral) => t
    case GreaterThan(a: IntegerLiteral, b: Variable) => t
    case GreaterThan(a: Variable, b: IntegerLiteral) => t
    case LessEquals(a: Variable, b: Variable) => t
    case LessEquals(a: IntegerLiteral, b: IntegerLiteral) => t
    case LessEquals(a: IntegerLiteral, b: Variable) => t
    case LessEquals(a: Variable, b: IntegerLiteral) => t
    case GreaterEquals(a: Variable, b: Variable) => t
    case GreaterEquals(a: IntegerLiteral, b: IntegerLiteral) => t
    case GreaterEquals(a: Variable, b: BooleanLiteral) => t
    case GreaterEquals(a: IntegerLiteral, b: Variable) => t
    case GreaterEquals(a: Variable, b: IntegerLiteral) => t
    case Equals(a: Variable, b: Variable) => t
    case Equals(a: BooleanLiteral, b: BooleanLiteral) => t
    case Equals(a: IntegerLiteral, b: IntegerLiteral) => t
    case Equals(a: IntegerLiteral, b: Variable) => t
    case Equals(a: Variable, b: IntegerLiteral) => t
    case Equals(a: BooleanLiteral, b: Variable) => t
    case Equals(a: Variable, b: BooleanLiteral) => t
    case Not(a: Variable) => t
    case Not(a: BooleanLiteral) => t
    case Plus(a: Variable, b: Variable) => t
    case Plus(a: IntegerLiteral, b: IntegerLiteral) => t
    case Plus(a: IntegerLiteral, b: Variable) => t
    case Plus(a: Variable, b: IntegerLiteral) => t
    case Minus(a: Variable, b: Variable) => t
    case Minus(a: IntegerLiteral, b: IntegerLiteral) => t
    case Minus(a: IntegerLiteral, b: Variable) => t
    case Minus(a: Variable, b: IntegerLiteral) => t
    case Times(a: Variable, b: Variable) => t
    case Times(a: IntegerLiteral, b: IntegerLiteral) => t
    case Times(a: IntegerLiteral, b: Variable) => t
    case Times(a: Variable, b: IntegerLiteral) => t
    case Division(a: Variable, b: Variable) => t
    case Division(a: IntegerLiteral, b: IntegerLiteral) => t
    case Division(a: IntegerLiteral, b: Variable) => t
    case Division(a: Variable, b: IntegerLiteral) => t
    case Remainder(a: Variable, b: Variable) => t
    case Remainder(a: IntegerLiteral, b: IntegerLiteral) => t
    case Remainder(a: IntegerLiteral, b: Variable) => t
    case Remainder(a: Variable, b: IntegerLiteral) => t
    case Modulo(a: Variable, b: Variable) => t
    case Modulo(a: IntegerLiteral, b: IntegerLiteral) => t
    case Modulo(a: IntegerLiteral, b: Variable) => t
    case Modulo(a: Variable, b: IntegerLiteral) => t
    case LessThan(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), LessThan(freshA, freshB)))
    case GreaterThan(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), GreaterThan(freshA, freshB)))
    case LessEquals(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), LessEquals(freshA, freshB)))
    case GreaterEquals(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), GreaterEquals(freshA, freshB)))
    // todo types for a, b
    case Equals(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, a.getType(using ctx.opts.symbols.get), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, b.getType(using ctx.opts.symbols.get), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), Equals(freshA, freshB)))
    case Not(a: Tree) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, BooleanType(), List())
      Let(freshA.toVal, insertLets(a), Not(freshA))
    case Plus(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), Plus(freshA, freshB)))
    case Minus(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), Minus(freshA, freshB)))
    case Times(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), Times(freshA, freshB)))
    case Division(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), Division(freshA, freshB)))
    case Remainder(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), Remainder(freshA, freshB)))
    case Modulo(a, b) =>
      val freshA = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      val freshB = Variable(new Identifier("tmp", 0, 0).freshen, IntegerType(), List())
      Let(freshA.toVal, insertLets(a), Let(freshB.toVal, insertLets(b), Modulo(freshA, freshB)))
    case Assume(pred, body) => Assume(pred, insertLets(body))
    case IsConstructor(e, id) => IsConstructor(insertLets(e), id)
    case _ => t


  var aprove: (Seq[Signature], Seq[Rule]) = (List(), List())
  var ctrl: (Seq[Signature], Seq[Rule]) = (List(), List())
  // existing INOX printing
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
    case IsConstructor(e, id) =>
      p"$e is $id"
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
      println(fd.id.uniqueName)
      println(fd.flags)
      // if(fd.id.name == "example") {

        //fd, 0 , f U (), (), (), ()
        val res = convert(fd, 0, Seq() ++ Seq(), fd.params.map(p => p.tpe match
          case ADTType(_, _) =>
            //println(ctx.opts.symbols.get)
              //.fields.map(f => VarT(f.id, f.tpe)).toList)
            VarT(p.id, p.tpe)
          case _ =>
            VarT(p.id, p.tpe)
        ), Seq(), Seq(), fd.fullBody)

        //val aprove = printAPROVE((res._1, res._2))
        //val ctrl = printCTRL((res._1, res._2))

        aprove = (aprove._1 ++ res._1, aprove._2 ++ res._2)
        ctrl = (ctrl._1 ++ res._1, ctrl._2 ++ res._2)

        val aproveMerge = printAPROVE(aprove)
        val ctrlMerge = printCTRL(ctrl)


        //println("CTRL export:")
        //println(ctrlMerge)
        //println("APROVE export:")
        //println(aproveMerge)

        val fw = new java.io.FileWriter("ctrl/example.ctrs");
        fw.write(ctrlMerge)
        fw.flush()
        fw.close()

        val fw_aprove = new java.io.FileWriter("aprove/example.itrs");
        fw_aprove.write(aproveMerge)
        fw_aprove.flush()
        fw_aprove.close()

      // }

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
                id.uniqueName
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
