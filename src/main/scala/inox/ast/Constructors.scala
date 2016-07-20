/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

/** Provides constructors for [[purescala.Expressions]].
  *
  * The constructors implement some logic to simplify the tree and
  * potentially use a different expression node if one is more suited.
  * @define encodingof Encoding of
  *  */
trait Constructors {
  val trees: Trees
  import trees._
  import trees.exprOps._
  implicit val symbols: Symbols
  import symbols._

  /** If `isTuple`:
    * `tupleSelect(tupleWrap(Seq(Tuple(x,y))),1) -> x`
    * `tupleSelect(tupleExpr,1) -> tupleExpr._1`
    * If not `isTuple` (usually used only in the case of a tuple of arity 1)
    * `tupleSelect(tupleWrap(Seq(Tuple(x,y))),1) -> Tuple(x,y)`.
    * @see [[purescala.Expressions.TupleSelect]]
    */
  def tupleSelect(t: Expr, index: Int, isTuple: Boolean): Expr = t match {
    case Tuple(es) if isTuple => es(index-1)
    case _ if t.getType.isInstanceOf[TupleType] && isTuple =>
      TupleSelect(t, index)
    case other if !isTuple => other
    case _ =>
      sys.error(s"Calling tupleSelect on non-tuple $t")
  }

  /** Simplifies the construct `TupleSelect(expr, index, originalSize > 1)`
    * @param originalSize The arity of the tuple. If less or equal to 1, the whole expression is returned.
    * @see [[purescala.Expressions.TupleSelect]]
    */
  def tupleSelect(t: Expr, index: Int, originalSize: Int): Expr = tupleSelect(t, index, originalSize > 1)

  /** $encodingof ``val id = e; bd``, and returns `bd` if the identifier is not bound in `bd`.
    * @see [[purescala.Expressions.Let]]
    */
  def let(vd: ValDef, e: Expr, bd: Expr) = {
    if (exprOps.variablesOf(bd) contains vd.toVariable)
      Let(vd, e, bd)
    else bd
  }

  /** $encodingof ``val (...binders...) = value; body`` which is translated to  ``value match { case (...binders...) => body }``, and returns `body` if the identifiers are not bound in `body`.
    * @see [[purescala.Expressions.Let]]
    */
  def letTuple(binders: Seq[ValDef], value: Expr, body: Expr) = binders match {
    case Nil =>
      body
    case x :: Nil =>
      Let(x, value, body)
    case xs =>
      require(
        value.getType match {
          case TupleType(args) => args.size == xs.size
          case _ => false
        },
        s"In letTuple: '$value' is being assigned as a tuple of arity ${xs.size}; yet its type is '${value.getType}' (body is '$body')"
      )

      LetPattern(TuplePattern(None,binders map { b => WildcardPattern(Some(b)) }), value, body)
  }

  /** Wraps the sequence of expressions as a tuple. If the sequence contains a single expression, it is returned instead.
    * @see [[purescala.Expressions.Tuple]]
    */
  def tupleWrap(es: Seq[Expr]): Expr = es match {
    case Seq() => UnitLiteral()
    case Seq(elem) => elem
    case more => Tuple(more)
  }

  /** Wraps the sequence of patterns as a tuple. If the sequence contains a single pattern, it is returned instead.
    * If the sequence is empty, [[purescala.Expressions.LiteralPattern `LiteralPattern`]]`(None, `[[purescala.Expressions.UnitLiteral `UnitLiteral`]]`())` is returned.
    * @see [[purescala.Expressions.TuplePattern]]
    * @see [[purescala.Expressions.LiteralPattern]]
    */
  def tuplePatternWrap(ps: Seq[Pattern]) = ps match {
    case Seq() => LiteralPattern(None, UnitLiteral())
    case Seq(elem) => elem
    case more => TuplePattern(None, more)
  }

  /** Wraps the sequence of types as a tuple. If the sequence contains a single type, it is returned instead.
    * If the sequence is empty, the [[purescala.Types.UnitType UnitType]] is returned.
    * @see [[purescala.Types.TupleType]]
    */
  def tupleTypeWrap(tps: Seq[Type]) = tps match {
    case Seq() => UnitType
    case Seq(elem) => elem
    case more => TupleType(more)
  }

  /** Instantiates the type parameters of the function according to argument types
    * @return A [[purescala.Expressions.FunctionInvocation FunctionInvocation]] if it type checks, else throws an error.
    * @see [[purescala.Expressions.FunctionInvocation]]
    */
  def functionInvocation(fd: FunDef, args: Seq[Expr]) = {
    require(fd.params.length == args.length, "Invoking function with incorrect number of arguments")

    val formalType = tupleTypeWrap(fd.params map { _.getType })
    val actualType = tupleTypeWrap(args map { _.getType })

    symbols.canBeSupertypeOf(formalType, actualType) match {
      case Some(tmap) =>
        FunctionInvocation(fd.id, fd.tparams map { tpd => tmap.getOrElse(tpd.tp, tpd.tp) }, args)
      case None => throw FatalError(s"$args:$actualType cannot be a subtype of $formalType!")
    }
  }

  /** Simplifies the provided case class selector.
    * @see [[purescala.Expressions.CaseClassSelector]]
    */
  def caseClassSelector(classType: ClassType, caseClass: Expr, selector: Identifier): Expr = {
    caseClass match {
      case CaseClass(ct, fields) if ct == classType && !ct.tcd.hasInvariant =>
        fields(ct.tcd.cd.asInstanceOf[CaseClassDef].selectorID2Index(selector))
      case _ =>
        CaseClassSelector(classType, caseClass, selector)
    }
  }

  /** $encoding of `case ... if ... => ... ` but simplified if possible, based on types of the encompassing [[purescala.Expressions.CaseClassPattern MatchExpr]].
    * @see [[purescala.Expressions.CaseClassPattern MatchExpr]]
    * @see [[purescala.Expressions.CaseClassPattern CaseClassPattern]]
    */
  private def filterCases(scrutType: Type, resType: Option[Type], cases: Seq[MatchCase]): Seq[MatchCase] = {
    val casesFiltered = scrutType match {
      case c: ClassType if !c.tcd.cd.isAbstract =>
        cases.filter(_.pattern match {
          case CaseClassPattern(_, cct, _) if cct.id != c.id => false
          case _ => true
        })

      case _ =>
        cases
    }

    resType match {
      case Some(tpe) =>
        casesFiltered.filter(c => symbols.typesCompatible(c.rhs.getType, tpe))
      case None =>
        casesFiltered
    }
  }

  /** $encodingof `... match { ... }` but simplified if possible. Simplifies to [[Error]] if no case can match the scrutined expression.
    * @see [[purescala.Expressions.MatchExpr MatchExpr]]
    */
  def matchExpr(scrutinee: Expr, cases: Seq[MatchCase]): Expr = {
    val filtered = filterCases(scrutinee.getType, None, cases)
    if (filtered.nonEmpty)
      MatchExpr(scrutinee, filtered)
    else
      Error(
        cases.headOption.map{ _.rhs.getType }.getOrElse(Untyped),
        "No case matches the scrutinee"
      )
  }

  /** $encodingof `&&`-expressions with arbitrary number of operands, and simplified.
    * @see [[purescala.Expressions.And And]]
    */
  def and(exprs: Expr*): Expr = {
    val flat = exprs.flatMap {
      case And(es) => es
      case o => Seq(o)
    }

    var stop = false
    val simpler = for(e <- flat if !stop && e != BooleanLiteral(true)) yield {
      if(e == BooleanLiteral(false)) stop = true
      e
    }

    simpler match {
      case Seq()  => BooleanLiteral(true)
      case Seq(x) => x
      case _      => And(simpler)
    }
  }

  /** $encodingof `&&`-expressions with arbitrary number of operands as a sequence, and simplified.
    * @see [[purescala.Expressions.And And]]
    */
  def andJoin(es: Seq[Expr]) = and(es :_*)

  /** $encodingof `||`-expressions with arbitrary number of operands, and simplified.
    * @see [[purescala.Expressions.Or Or]]
    */
  def or(exprs: Expr*): Expr = {
    val flat = exprs.flatMap {
      case Or(es) => es
      case o => Seq(o)
    }

    var stop = false
    val simpler = for(e <- flat if !stop && e != BooleanLiteral(false)) yield {
      if(e == BooleanLiteral(true)) stop = true
      e
    }

    simpler match {
      case Seq()  => BooleanLiteral(false)
      case Seq(x) => x
      case _      => Or(simpler)
    }
  }

  /** $encodingof `||`-expressions with arbitrary number of operands as a sequence, and simplified.
    * @see [[purescala.Expressions.Or Or]]
    */
  def orJoin(es: Seq[Expr]) = or(es :_*)

  /** $encodingof simplified `!`-expressions .
    * @see [[purescala.Expressions.Not Not]]
    */
  def not(e: Expr): Expr = negate(e)

  /** $encodingof simplified `... ==> ...` (implication)
    * @see [[purescala.Expressions.Implies Implies]]
    */
  def implies(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (BooleanLiteral(false), _) => BooleanLiteral(true)
    case (_, BooleanLiteral(true))  => BooleanLiteral(true)
    case (BooleanLiteral(true), r)  => r
    case (l, BooleanLiteral(false)) => Not(l)
    case (l1, Implies(l2, r2))      => implies(and(l1, l2), r2)
    case _                          => Implies(lhs, rhs)
  }

  /** $encodingof simplified `... == ...` (equality).
    * @see [[purescala.Expressions.Equals Equals]]
    */
  // @mk I simplified that because it seemed dangerous and unnessecary
  def equality(a: Expr, b: Expr): Expr = {
    if (a.isInstanceOf[Terminal] && isPurelyFunctional(a) && a == b ) {
      BooleanLiteral(true)
    } else  {
      Equals(a, b)
    }
  }

  def assertion(c: Expr, err: Option[String], res: Expr) = {
    if (c == BooleanLiteral(true)) {
      res
    } else if (c == BooleanLiteral(false)) {
      Error(res.getType, err.getOrElse("Assertion failed"))
    } else {
      Assert(c, err, res)
    }
  }

  /** $encodingof simplified `fn(realArgs)` (function application).
    * Transforms
    * {{{ ((x: A, y: B) => g(x, y))(c, d) }}}
    * into
    * {{{val x0 = c
    * val y0 = d
    * g(x0, y0)}}}
    * and further simplifies it.
    * @see [[purescala.Expressions.Lambda Lambda]]
    * @see [[purescala.Expressions.Application Application]]
    */
  def application(fn: Expr, realArgs: Seq[Expr]) = fn match {
     case Lambda(formalArgs, body) =>
      assert(realArgs.size == formalArgs.size, "Invoking lambda with incorrect number of arguments")

      var defs: Seq[(ValDef, Expr)] = Seq()

      val subst = formalArgs.zip(realArgs).map {
        case (vd, to:Variable) =>
          vd -> to
        case (vd, e) =>
          val fresh = vd.freshen
          defs :+= (fresh -> e)
          vd -> fresh.toVariable
      }.toMap

      val (vds, bds) = defs.unzip

      letTuple(vds, tupleWrap(bds), exprOps.replaceFromSymbols(subst, body))

    case _ =>
      Application(fn, realArgs)
   }

  /** $encodingof simplified `... + ...` (plus).
    * @see [[purescala.Expressions.Plus Plus]]
    * @see [[purescala.Expressions.BVPlus BVPlus]]
    * @see [[purescala.Expressions.RealPlus RealPlus]]
    */
  def plus(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (IntegerLiteral(bi), _) if bi == 0 => rhs
    case (_, IntegerLiteral(bi)) if bi == 0 => lhs
    case (IntLiteral(0), _) => rhs
    case (_, IntLiteral(0)) => lhs
    case (FractionalLiteral(n, d), _) if n == 0 => rhs
    case (_, FractionalLiteral(n, d)) if n == 0 => lhs
    case _ => Plus(lhs, rhs)
  }

  /** $encodingof simplified `... - ...` (minus).
    * @see [[purescala.Expressions.Minus Minus]]
    * @see [[purescala.Expressions.BVMinus BVMinus]]
    * @see [[purescala.Expressions.RealMinus RealMinus]]
    */
  def minus(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (_, IntegerLiteral(bi)) if bi == 0 => lhs
    case (_, IntLiteral(0)) => lhs
    case (IntegerLiteral(bi), _) if bi == 0 => UMinus(rhs)
    case _ => Minus(lhs, rhs)
  }

  def uminus(e: Expr): Expr = e match {
    case IntegerLiteral(bi) if bi == 0 => e
    case IntLiteral(0) => e
    case IntegerLiteral(bi) if bi < 0 => IntegerLiteral(-bi)
    case UMinus(i) if i.getType == IntegerType => i
    case _ => UMinus(e)
  }

  /** $encodingof simplified `... * ...` (times).
    * @see [[purescala.Expressions.Times Times]]
    * @see [[purescala.Expressions.BVTimes BVTimes]]
    * @see [[purescala.Expressions.RealTimes RealTimes]]
    */
  def times(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (IntegerLiteral(bi), _) if bi == 1 => rhs
    case (_, IntegerLiteral(bi)) if bi == 1 => lhs
    case (IntegerLiteral(bi), _) if bi == 0 => IntegerLiteral(0)
    case (_, IntegerLiteral(bi)) if bi == 0 => IntegerLiteral(0)
    case (IntLiteral(1), _) => rhs
    case (_, IntLiteral(1)) => lhs
    case (IntLiteral(0), _) => IntLiteral(0)
    case (_, IntLiteral(0)) => IntLiteral(0)
    case _ => Times(lhs, rhs)
  }

  /** $encodingof expr.asInstanceOf[tpe], returns `expr` it it already is of type `tpe`.  */
  def asInstOf(expr: Expr, tpe: ClassType) = {
    if (symbols.isSubtypeOf(expr.getType, tpe)) {
      expr
    } else {
      AsInstanceOf(expr, tpe)
    }
  }

  def isInstOf(expr: Expr, tpe: ClassType) = {
    if (symbols.isSubtypeOf(expr.getType, tpe)) {
      BooleanLiteral(true)
    } else {
      IsInstanceOf(expr, tpe)
    }
  }

  def req(pred: Expr, body: Expr) = pred match {
    case BooleanLiteral(true)  => body
    case BooleanLiteral(false) => Error(body.getType, "Precondition failed")
    case _ => Require(pred, body)
  }

  def tupleWrapArg(fun: Expr) = fun.getType match {
    case FunctionType(args, res) if args.size > 1 =>
      val newArgs = fun match {
        case Lambda(args, _) => args
        case _ => args map (tpe => ValDef(FreshIdentifier("x", alwaysShowUniqueID = true), tpe))
      }
      val res = ValDef(FreshIdentifier("res", alwaysShowUniqueID = true), TupleType(args))
      val patt = TuplePattern(None, newArgs map (arg => WildcardPattern(Some(arg))))
      Lambda(Seq(res), MatchExpr(res.toVariable, Seq(SimpleCase(patt, application(fun, newArgs map (_.toVariable))))))
    case _ =>
      fun
  }

  def ensur(e: Expr, pred: Expr) = {
    Ensuring(e, tupleWrapArg(pred))
  }

}