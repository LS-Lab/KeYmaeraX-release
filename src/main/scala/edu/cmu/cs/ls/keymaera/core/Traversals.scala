package edu.cmu.cs.ls.keymaera.core

import java.util

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal._

/**
 * This object holds some useful traversals.
 * Tested by TraversalTests.
 * Created by nfulton on 12/31/14.
 */
object Traversals {

  /**
   * @todo this implementation is incorrect -- we'll return bound variables as well. Need to flip a counter when
   *       entering and exiting quantified subexpressions.
   * @param expression
   * @return A lsit of all free variables in the expression.
   */
  def freeVariables(expression : Expr) : List[Variable] = {
    val traversal = new ExpressionTraversalFunction {
      /**
       * Variables are only free when binding == 0.
       * binding is incremented when entering a quantified formula and decremented when leaving.
       */
      var binding : Int = 0
      var variables : List[Variable] = Nil

      override def preF(p : PosInExpr, f : Formula) = {
        f match {
          case f : Quantifier => {
            binding = binding + 1;
          }
          case _ => /* nothing to do here */
        };
        Left(None)
      }
      override def postF(p : PosInExpr, f : Formula) = {
        f match {
          case f : Quantifier => {
            binding = binding - 1;
          }
          case _ => /* nothing to do here */
        };
        Left(None)
      }

      override def preT(p : PosInExpr, e : Term) = {
        e match {
          case e : Variable => {
            if(!variables.contains(e) && binding == 0) {
              variables = e +: variables
            }
          }
          case _ => /* nothing to do here */
        };
        Left(None)
      }
    }

    expression match {
      case expression : Formula => ExpressionTraversal.traverse(traversal, expression)
      case expression : Term => ExpressionTraversal.traverse(traversal, expression)
      case expression : Program => ExpressionTraversal.traverse(traversal, expression)
      case _ => ???
    }

    traversal.variables
  }
}
