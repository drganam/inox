/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers.z3

import z3.scala.{Z3Optimizer => ScalaZ3Optimizer, _}
import Z3Native._
import solvers._
import unrolling._

trait NativeZ3Optimizer extends AbstractUnrollingOptimizer with Z3Unrolling { self =>

  import program._
  import program.trees._
  import program.symbols._

  override val name = "native-z3-opt"

  protected val underlying = NativeZ3Solver.synchronized(new {
    val program: targetProgram.type = targetProgram
    val context = self.context
  } with AbstractOptimizer with Z3Native {
    import program._
    import program.trees._
    import program.symbols._

    import SolverResponses._

    val name = "z3-opt"

    private[this] val optimizer: ScalaZ3Optimizer = z3.mkOptimizer()

    def assertCnstr(ast: Z3AST): Unit = tryZ3(optimizer.assertCnstr(ast))
    def assertCnstr(ast: Z3AST, weight: Int): Unit = tryZ3(optimizer.assertCnstr(ast, weight))
    def assertCnstr(ast: Z3AST, weight: Int, group: String): Unit = tryZ3(optimizer.assertCnstr(ast, weight, group))

    def maximize(ast: Z3AST): Unit = tryZ3(optimizer.maximize(ast))
    def minimize(ast: Z3AST): Unit = tryZ3(optimizer.minimize(ast))

    // NOTE @nv: this is very similar to code in AbstractZ3Solver and UninterpretedZ3Solver but
    //           is difficult to merge due to small API differences between the native Z3
    //           solvers and optimizers.
    def check(config: CheckConfiguration) = config.cast(tryZ3(optimizer.check() match {
      case Some(true) => if (config.withModel) SatWithModel(optimizer.getModel()) else Sat
      case Some(false) => Unsat
      case None => Unknown
    }).getOrElse(Unknown))

    // NOTE @nv: this is very similar to code in AbstractZ3Solver and UninterpretedZ3Solver but
    //           is difficult to merge due to small API differences between the native Z3
    //           solvers and optimizers.
    def checkAssumptions(config: Configuration)(assumptions: Set[Z3AST]) = {
      optimizer.push()
      for (a <- assumptions) optimizer.assertCnstr(a)
      val res = config.cast(tryZ3[SolverResponse[Model, Assumptions]](optimizer.check() match {
        case Some(true) => if (config.withModel) SatWithModel(optimizer.getModel()) else Sat
        case Some(false) => if (config.withUnsatAssumptions) UnsatWithAssumptions(Set()) else Unsat
        case None => Unknown
      }).getOrElse(Unknown))
      optimizer.pop()
      res
    }

    lazy val semantics = targetSemantics

    override def push(): Unit = {
      super.push()
      optimizer.push()
    }

    override def pop(): Unit = {
      super.pop()
      optimizer.pop()
    }
  })

  override def free(): Unit = NativeZ3Solver.synchronized(super.free())
}
