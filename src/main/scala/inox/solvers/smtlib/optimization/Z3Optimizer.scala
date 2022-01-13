/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib
package optimization

import Commands._

trait Z3Optimizer extends Z3Solver with AbstractOptimizer {
  import program._
  import program.trees._
  import program.symbols.{given, _}

  def assertCnstr(expr: Expr, weight: Int): Unit = {
    exprOps.variablesOf(expr).foreach(declareVariable)

    val term = toSMT(expr)(using Map())
    emit(AssertSoft(term, Some(weight), None))
  }

  def assertCnstr(expr: Expr, weight: Int, group: String): Unit = {
    exprOps.variablesOf(expr).foreach(declareVariable)

    val term = toSMT(expr)(using Map())
    emit(AssertSoft(term, Some(weight), Some(group)))
  }

  def minimize(expr: Expr): Unit = {
    exprOps.variablesOf(expr).foreach(declareVariable)

    val term = toSMT(expr)(using Map())
    emit(Minimize(term))
  }

  def maximize(expr: Expr): Unit = {
    exprOps.variablesOf(expr).foreach(declareVariable)

    val term = toSMT(expr)(using Map())
    emit(Maximize(term))
  }
}
