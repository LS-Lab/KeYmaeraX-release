package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._

/**
 * Simple recursion schemes for expressions.
 * @author Nathan Fulton
 */
object ExpressionRecursor {
  /**
   * A very simple recusion principle for expressions.
   * I couldn't figure out how to do this using the epxression traversal library.
   * @param T the return type.
   * @param e The expression to recurse on
   * @param f A function for processing stopping points in the recursion (nullary expressions and anything specified by partialStop)
   * @param join A function for joining a list of T's returned from binary or ternary expressions.
   * @param partialStop A function specifying where recursion should be cut short.
   */
  def ePartRec[T](e : Expr, f : Expr => T, join : List[T] => T, partialStop : Expr => Boolean) : T = {
    if(partialStop(e)) f(e) //note: we also return f(e) when e in nullary and no recursion is possible.
    else e match {
      case e : Unary   => ePartRec(e.child, f, join, partialStop)
      case e : Binary  => {
        val l = ePartRec(e.left,f,join,partialStop)
        val r = ePartRec(e.right,f,join,partialStop)
        join(List(l,r))
      }
      case e : Ternary => {
        val one = ePartRec(e.fst,f,join,partialStop)
        val two = ePartRec(e.snd,f,join,partialStop)
        val three = ePartRec(e.thd,f,join,partialStop)
        join(List(one,two,three))
      }
      case True()      => f(e)
      case False()     => f(e)
      case e : NamedSymbol => f(e)
      case e : Number.NumberObj => f(e)
      case AtomicContEvolve(x: Term, theta: Term) => {
        val xResult       = ePartRec(x,f,join,partialStop)
        val thetaResult   = ePartRec(theta,f,join,partialStop)
        join(List(xResult, thetaResult))
      }
    }
  }

  /**
   * Example: get free variables using the recursion mechanism.
   */
  def getFreeVariables(e : Expr) : List[NamedSymbol] = {
    type T = List[NamedSymbol]
    
    def f(ignoreList : List[NamedSymbol] = List())(expr : Expr) : T = expr match {
      case expr : NamedSymbol => {
        if(ignoreList.contains(expr)) {
          List()
        }
        else {
          List(expr)
        }
      }
      case expr : Quantifier  => {
        //Recurse, ignoring the bound variable.
        ePartRec(e, f(ignoreList ++ expr.variables), join, partialStop)
      }
    }
    
    def join(list : List[T]) = list.reduce(_ ++ _)
    
    //The partialStop function must prevent recursion into binding sites.
    def partialStop(expr : Expr) : Boolean = expr match {
      case expr : Quantifier => true
      case _ => false //TODO-nrf anything else?
    }
    
    ePartRec(e, f(), join, partialStop)
  }
}