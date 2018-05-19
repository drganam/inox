/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers.z3

import com.microsoft.z3.Z3Exception

import z3.scala._

import solvers._
import utils.IncrementalSet

/** This is a rather direct mapping to Z3, where all functions are left uninterpreted.
 *  It reports the results as follows (based on the negation of the formula):
 *    - if Z3 reports UNSAT, it reports VALID
 *    - if Z3 reports SAT and the formula contained no function invocation, it returns INVALID with the counter-example/model
 *    - otherwise it returns UNKNOWN
 *  Results should come back very quickly.
 */
trait UninterpretedZ3Solver
  extends Solver { self =>

  import context._
  import program.{symbols => _, _}
  import program.trees._
  import program.symbols._

  import SolverResponses._

  protected implicit val semantics: program.Semantics

  val name = "z3-u"
  val description = "Uninterpreted Z3 Solver"

  private val underlying = {
    class UnderlyingSolverBase(val program: self.program.type, val context: Context) extends AbstractZ3Solver {
      val semantics = self.semantics
    }
    new UnderlyingSolverBase(self.program, self.context)
  }

  private val freeVars = new IncrementalSet[Variable]

  def push(): Unit = {
    underlying.push()
    freeVars.push()
  }

  def pop(): Unit = {
    underlying.pop()
    freeVars.pop()
  }

  def reset(): Unit = {
    underlying.reset()
    freeVars.reset()
  }

  def free(): Unit = underlying.free()

  def interrupt(): Unit = underlying.interrupt()

  def assertCnstr(expression: Expr): Unit = {
    freeVars ++= exprOps.variablesOf(expression)
    tryZ3(underlying.assertCnstr(underlying.toZ3Formula(expression)))
  }

  private def completeModel(model: program.Model): program.Model = {
    val allVars = freeVars.map(v => v.toVal -> model.vars.getOrElse(v.toVal, simplestValue(v.getType))).toMap
    inox.Model(program, context)(allVars, model.chooses)
  }

  private def tryZ3[T](res: => T): Option[T] =
    // @nv: Z3 sometimes throws an exception when check is called after Z3 has been canceled
    try { Some(res) } catch {  case e: Z3Exception if e.getMessage == "canceled" => None }

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    config.convert(
      tryZ3(underlying.check(config)).getOrElse(config.cast(Unknown))
        .asInstanceOf[config.Response[Z3Model, Set[Z3AST]]],  // NOTE(gsps): [Dotty bug] Why can't dotty prove this on its own?
      (model: Z3Model) => completeModel(underlying.extractModel(model)),
      underlying.extractUnsatAssumptions)

  override def checkAssumptions(config: Configuration)
                               (assumptions: Set[Expr]): config.Response[Model, Assumptions] =
    config.convert[Z3Model, Z3AST, Model, Expr](
      tryZ3(underlying.checkAssumptions(config)(assumptions.map(underlying.toZ3Formula(_))))
        .getOrElse(config.cast(Unknown)),
      (model: Z3Model) => completeModel(underlying.extractModel(model)),
      underlying.extractUnsatAssumptions)
}
