/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

class ExprOpsSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import inox.trees.exprOps.{given, _}

  given ctx0: Context = TestContext.empty

  private def foldConcatNames(e: Expr, subNames: Seq[String]): String = e match {
    case Variable(id, _, _) => subNames.mkString + id.name
    case _ => subNames.mkString
  }

  private def foldCountVariables(e: Expr, subCounts: Seq[Int]): Int = e match {
    case Variable(_, _, _) => subCounts.sum + 1
    case _ => subCounts.sum
  }

  val a = Variable.fresh("a", Int32Type())
  val b = Variable.fresh("b", Int32Type())

  val x = Variable.fresh("x", IntegerType())
  val y = Variable.fresh("y", IntegerType())

  val p = Variable.fresh("p", BooleanType())
  val q = Variable.fresh("q", BooleanType())
  val r = Variable.fresh("r", BooleanType())

  test("foldRight works on single variable expression") {
    assert(fold(foldConcatNames)(x) === x.id.name)
    assert(fold(foldConcatNames)(y) === y.id.name)
    assert(fold(foldCountVariables)(x) === 1)
    assert(fold(foldCountVariables)(y) === 1)
  }

  test("foldRight works on simple expressions without nested structure") {
    assert(fold(foldConcatNames)(And(p, q)) === (p.id.name + q.id.name))
    assert(fold(foldConcatNames)(And(q, p)) === (q.id.name + p.id.name))
    assert(fold(foldConcatNames)(And(Seq(p, p, p, q, r))) ===
           (p.id.name + p.id.name + p.id.name + q.id.name + r.id.name))
    assert(fold(foldConcatNames)(Or(Seq(p, p, p, q, r))) ===
           (p.id.name + p.id.name + p.id.name + q.id.name + r.id.name))
    assert(fold(foldConcatNames)(Plus(x, y)) === (x.id.name + y.id.name))

    assert(fold(foldCountVariables)(And(p, q)) === 2)
    assert(fold(foldCountVariables)(And(q, p)) === 2)
    assert(fold(foldCountVariables)(And(p, p)) === 2)
    assert(fold(foldCountVariables)(And(Seq(p, p, p, q, r))) === 5)
    assert(fold(foldCountVariables)(Or(Seq(p, p, p, q, r))) === 5)
  }

  test("foldRight works on simple structure of nested expressions") {
    assert(fold(foldConcatNames)(And(And(p, q), r)) === (p.id.name + q.id.name + r.id.name))
    assert(fold(foldConcatNames)(And(p, Or(q, r))) === (p.id.name + q.id.name + r.id.name))
  }

  private class LocalCounter {
    private var c = 0
    def inc() = c += 1
    def get = c
  }

  test("preTraversal works on a single node") {
    val c = new LocalCounter
    preTraversal(e => c.inc())(x)
    assert(c.get === 1)
    preTraversal(e => c.inc())(y)
    assert(c.get === 2)

    var names: List[String] = List()
    preTraversal({
      case Variable(id, _, _) => names ::= id.name
      case _ => ()
    })(x)
    assert(names === List(x.id.name))
  }

  test("preTraversal correctly applies on every nodes on a simple expression") {
    val c1 = new LocalCounter
    preTraversal(e => c1.inc())(And(Seq(p, q, r)))
    assert(c1.get === 4)
    val c2 = new LocalCounter
    preTraversal(e => c2.inc())(Or(p, q))
    assert(c2.get === 3)
    preTraversal(e => c2.inc())(Plus(x, y))
    assert(c2.get === 6)
  }

  test("preTraversal visits children from left to right") {
    var names: List[String] = List()
    preTraversal({
      case Variable(id, _, _) => names ::= id.name
      case _ => ()
    })(And(List(p, q, r)))
    assert(names === List(r.id.name, q.id.name, p.id.name))
  }

  test("preTraversal works on nexted expressions") {
    val c = new LocalCounter
    preTraversal(e => c.inc())(And(p, And(q, r)))
    assert(c.get === 5)
  }

  test("preTraversal traverses in pre-order") {
    var nodes: List[Expr] = List()
    val node = And(List(p, q, r))
    preTraversal(e => nodes ::= e)(node)
    assert(nodes === List(r, q, p, node))
  }


  test("postTraversal works on a single node") {
    val c = new LocalCounter
    postTraversal(e => c.inc())(x)
    assert(c.get === 1)
    postTraversal(e => c.inc())(y)
    assert(c.get === 2)

    var names: List[String] = List()
    postTraversal({
      case Variable(id, _, _) => names ::= id.name
      case _ => ()
    })(x)
    assert(names === List(x.id.name))
  }

  test("postTraversal correctly applies on every nodes on a simple expression") {
    val c1 = new LocalCounter
    postTraversal(e => c1.inc())(And(Seq(p, q, r)))
    assert(c1.get === 4)
    val c2 = new LocalCounter
    postTraversal(e => c2.inc())(Or(p, q))
    assert(c2.get === 3)
    postTraversal(e => c2.inc())(Plus(x, y))
    assert(c2.get === 6)
  }

  test("postTraversal visits children from left to right") {
    var names: List[String] = List()
    postTraversal({
      case Variable(id, _, _) => names ::= id.name
      case _ => ()
    })(And(List(p, q, r)))
    assert(names === List(r.id.name, q.id.name, p.id.name))
  }

  test("postTraversal works on nexted expressions") {
    val c = new LocalCounter
    postTraversal(e => c.inc())(And(p, And(q, r)))
    assert(c.get === 5)
  }

  test("postTraversal traverses in pre-order") {
    var nodes: List[Expr] = List()
    val node = And(List(p, q, r))
    postTraversal(e => nodes ::= e)(node)
    assert(nodes === List(node, r, q, p))
  }

  /**
   * If the formula consist of some top level AND, find a top level
   * Equals and extract it, return the remaining formula as well
   */
  def extractEquals(expr: Expr): (Option[Equals], Expr) = expr match {
    case And(es) =>
      // OK now I'm just messing with you.
      val (r, nes) = es.foldLeft[(Option[Equals],Seq[Expr])]((None, Seq())) {
        case ((None, nes), eq @ Equals(_,_)) => (Some(eq), nes)
        case ((o, nes), e) => (o, e +: nes)
      }
      (r, And(nes.reverse))

    case e => (None, e)
  }

  def testSimplifyArithmetic(litCtor: BigInt => Expr): Unit = {
    val syms = new Symbols(Map.empty, Map.empty)
    object program extends Program {
      val trees: inox.trees.type = inox.trees
      val symbols: syms.type = syms
      val ctx = ctx0
    }
    import syms.given
    val ev = evaluators.RecursiveEvaluator(program, ctx0)

    def checkEq(e1: Expr, e2: Expr): Unit = {
      val r1 = ev.eval(e1)
      val r2 = ev.eval(e2)
      assert(r1 === r2, s"'$e1' != '$e2' ('$r1' != '$r2')")
    }

    val e1 = Plus(litCtor(3), litCtor(2))
    checkEq(e1, simplifyArithmetic(e1))
    val e2 = Plus(x, Plus(litCtor(3), litCtor(2)))
    checkEq(e2, simplifyArithmetic(e2))

    val e3 = Minus(litCtor(3), litCtor(2))
    checkEq(e3, simplifyArithmetic(e3))
    val e4 = Plus(x, Minus(litCtor(3), litCtor(2)))
    checkEq(e4, simplifyArithmetic(e4))
    val e5 = Plus(x, Minus(x, litCtor(2)))
    checkEq(e5, simplifyArithmetic(e5))

    val e6 = Times(litCtor(9), Plus(Division(x, litCtor(3)), Division(x, litCtor(6))))
    checkEq(e6, simplifyArithmetic(e6))
  }

  test("simplifyArithmetic") {
    testSimplifyArithmetic(IntegerLiteral.apply)
    for {
      signed <- List(false, true)
      size <- List(8, 16, 32)
    } testSimplifyArithmetic(BVLiteral(signed, _, size))
  }

  test("extractEquals") {
    val eq = Equals(a, b)
    val lt1 = LessThan(a, b)
    val lt2 = LessThan(b, a)
    val lt3 = LessThan(x, y)

    val f1 = And(Seq(eq, lt1, lt2, lt3))
    val (eq1, r1) = extractEquals(f1)
    assert(eq1 != None)
    assert(eq1.get === eq)
    assert(extractEquals(r1)._1 === None)

    val f2 = And(Seq(lt1, lt2, eq, lt3))
    val (eq2, r2) = extractEquals(f2)
    assert(eq2 != None)
    assert(eq2.get === eq)
    assert(extractEquals(r2)._1 === None)

    val f3 = And(Seq(lt1, eq, lt2, lt3, eq))
    val (eq3, r3) = extractEquals(f3)
    assert(eq3 != None)
    assert(eq3.get === eq)
    val (eq4, r4) = extractEquals(r3)
    assert(eq4 != None)
    assert(eq4.get === eq)
    assert(extractEquals(r4)._1 === None)
  }

  test("pre and post traversal") {
    val expr = Plus(IntegerLiteral(1), Minus(IntegerLiteral(2), IntegerLiteral(3)))
    var res = ""
    def f(e: Expr): Unit = e match {
      case IntegerLiteral(i) => res += i
      case _ : Plus      => res += "P"
      case _ : Minus     => res += "M"
    }

    preTraversal(f)(expr)
    assert(res === "P1M23")

    res = ""
    postTraversal(f)(expr)
    assert(res === "123MP")
  }

  test("pre- and postMap") {
    val expr = Plus(IntegerLiteral(1), Minus(IntegerLiteral(2), IntegerLiteral(3)))
    def op(e : Expr ) = e match {
      case Minus(IntegerLiteral(two), e2) if two == BigInt(2) => Some(IntegerLiteral(2))
      case IntegerLiteral(one) if one == BigInt(1) => Some(IntegerLiteral(2))
      case IntegerLiteral(two) if two == BigInt(2) => Some(IntegerLiteral(42))
      case _ => None
    }

    assert( preMap(op, false)(expr) == Plus(IntegerLiteral(2),  IntegerLiteral(2))  )
    assert( preMap(op, true )(expr) == Plus(IntegerLiteral(42), IntegerLiteral(42)) )
    assert( postMap(op, false)(expr) == Plus(IntegerLiteral(2),  Minus(IntegerLiteral(42), IntegerLiteral(3))) )
    assert( postMap(op, true)(expr)  == Plus(IntegerLiteral(42), Minus(IntegerLiteral(42), IntegerLiteral(3))) )
  }

  test("simplestValue") {
    val syms = new Symbols(Map.empty, Map.empty)
    object program extends Program {
      val trees: inox.trees.type = inox.trees
      val symbols: syms.type = syms
      val ctx = ctx0
    }

    import program.{given, _}
    import program.trees.{given, _}
    import program.symbols.{given, _}

    val types = Seq(BooleanType(),
                    Int32Type(),
                    IntegerType(),
                    SetType(BooleanType()),
                    TupleType(Seq(BooleanType(), BooleanType())),
                    MapType(Int32Type(), BooleanType()))

    for (t <- types) {
      val v = simplestValue(t)
      assert(isSubtypeOf(v.getType, t), "SimplestValue of "+t+": "+v+":"+v.getType)
    }
  }

  test("preMapWithContext") {
    val expr = Plus(IntegerLiteral(1), Minus(IntegerLiteral(2), IntegerLiteral(3)))
    def op(e : Expr, set: Set[Int]): (Option[Expr], Set[Int]) = e match {
      case Minus(IntegerLiteral(two), e2) if two == BigInt(2) => (Some(IntegerLiteral(2)), set)
      case IntegerLiteral(one) if one == BigInt(1) => (Some(IntegerLiteral(2)), set)
      case IntegerLiteral(two) if two == BigInt(2) => (Some(IntegerLiteral(42)), set)
      case _ => (None, set)
    }

    assert(preMapWithContext(op, false)(expr, Set()) === Plus(IntegerLiteral(2),  IntegerLiteral(2)))
    assert(preMapWithContext(op, true)(expr, Set()) === Plus(IntegerLiteral(42),  IntegerLiteral(42)))

    val expr2 = Let(x.toVal, IntegerLiteral(1), Let(y.toVal, IntegerLiteral(2), Plus(x, y)))
    def op2(e: Expr, bindings: Map[Variable, BigInt]): (Option[Expr], Map[Variable, BigInt]) = e match {
      case Let(vd, IntegerLiteral(v), body) => (None, bindings + (vd.toVariable -> v))
      case v: Variable => (bindings.get(v).map(value => IntegerLiteral(value)), bindings)
      case _ => (None, bindings)
    }

    assert(preMapWithContext(op2, false)(expr2, Map()) === Let(
      x.toVal, IntegerLiteral(1), Let(y.toVal, IntegerLiteral(2), Plus(IntegerLiteral(1), IntegerLiteral(2)))))

    def op3(e: Expr, bindings: Map[Variable, BigInt]): (Option[Expr], Map[Variable, BigInt]) = e match {
      case Let(vd, IntegerLiteral(v), body) => (Some(body), bindings + (vd.toVariable -> v))
      case v: Variable => (bindings.get(v).map(v => IntegerLiteral(v)), bindings)
      case _ => (None, bindings)
    }
    assert(preMapWithContext(op3, true)(expr2, Map()) === Plus(IntegerLiteral(1), IntegerLiteral(2)))


    val expr4 = Plus(Let(y.toVal, IntegerLiteral(2), y),
                     Let(y.toVal, IntegerLiteral(4), y))
    def op4(e: Expr, bindings: Map[Variable, BigInt]): (Option[Expr], Map[Variable, BigInt]) = e match {
      case Let(vd, IntegerLiteral(v), body) =>
        (Some(body), if (bindings.contains(vd.toVariable)) bindings else (bindings + (vd.toVariable -> v)))
      case v: Variable => (bindings.get(v).map(v => IntegerLiteral(v)), bindings)
      case _ => (None, bindings)
    }
    assert(preMapWithContext(op4, true)(expr4, Map()) === Plus(IntegerLiteral(2), IntegerLiteral(4)))
  }

}
