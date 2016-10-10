/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Context._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._

import scala.collection.immutable._

/**
  * Tactics for introducing interval arithmetic.
  *
  * @author Yong Kiam Tan
  */
object IntervalArithmetic {

  private val ubPrefix = "u"
  private val lbPrefix = "l"

  def getBounds(f:Formula) =
    symbols(f).map(t => List(LessEqual(FuncOf(Function(lbPrefix,None,Real,Real),t),t),
                         LessEqual(t,FuncOf(Function(ubPrefix,None,Real,Real),t)))).flatten

  //Same as symbols in TacticHelper, returns the set of vars and nullary function symbols
  //todo: Ensure that the upper and lower bound prefixes do not appear inside
  def symbols(f: Formula): Set[Term] = {
    var symbols = Set[Term]()
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
        case v: Variable => symbols += v; Left(None)
        case FuncOf(fn: Function, u:AtomicTerm) => if(u==Nothing) symbols += e; Left(None)
        case _ => Left(None)
      }
    }, f)
    symbols
  }

  //Flips >= and >, and splits < and <= into two interval checks
  lazy val splitGreaterEqual: DependentPositionTactic = chaseI(5, 5, (exp: Expression) => exp match {
    case And(_,_) => "& recursor" :: Nil
    case Or(_,_) => "| recursor" :: Nil
    case GreaterEqual(_,_) => ">= flip" :: Nil
    case Greater(_,_) => "> flip" :: Nil
    case LessEqual(_,_) => "<= both" :: Nil
    case Less(_,_) => "< both" :: Nil
    case _ => Nil
  },
    (ax:String) => (us:Subst) => ax match {
      case "<= both" | "< both" => us ++ RenUSubst(
        ("F_()".asTerm, FuncOf(Function(ubPrefix,None,Real,Real), us("f_()".asTerm))) ::
          ("G_()".asTerm, FuncOf(Function(ubPrefix,None,Real,Real), us("g_()".asTerm))) ::
          ("ff_()".asTerm, FuncOf(Function(lbPrefix,None,Real,Real), us("f_()".asTerm))) ::
          ("gg_()".asTerm, FuncOf(Function(lbPrefix,None,Real,Real), us("g_()".asTerm))) ::
          Nil)
      case _ => us
    })

  //Normalizes to a simpler grammar with no negatives
  lazy val simplifyEqns: DependentPositionTactic = chaseI(5, 5, (exp: Expression) => exp match {
    case And(_,_) => "& recursor" :: Nil
    case Or(_,_) => "| recursor" :: Nil
    case Imply(_,_) => "-> expand" :: Nil
    case Not(_) => AxiomIndex.axiomsFor(exp)
    case _ => Nil
  },
    ax => us => us
  )

  //Chases intervals inwards
  lazy val intervalify: DependentPositionTactic = chaseI(5, 5, (exp: Expression) => exp match {
    case And(_,_) => "& recursor" :: Nil
    case Or(_,_) => "| recursor" :: Nil
    case LessEqual(FuncOf(Function(lbPrefix,_,_,_,_),_),rhs) =>
      rhs match{
        case Plus(_,_) => "<=+ down" :: Nil
        case Minus(_,_) => "<=- down" :: Nil
        case Times(_,_) => "<=* down" :: Nil
        case Divide(_,_) => "<=Div down" :: Nil
        case Power(_,_) => "<=pow down" :: Nil
        case FuncOf(Function("abs",_,_,_,_),_) => "<=abs down" :: Nil
        case _ => Nil
      }
    case LessEqual(lhs,FuncOf(Function(ubPrefix,_,_,_,_),_)) =>
      lhs match{
        case Plus(_,_) => "+<= up" :: Nil
        case Minus(_,_) => "-<= up" :: Nil
        case Times(_,_) => "*<= up" :: Nil
        case Divide(_,_) => "Div<= up" :: Nil
        case Power(_,_) => "pow<= up" :: Nil
        case FuncOf(Function("abs",_,_,_,_),_) => "abs<= up" :: Nil
        case _ => Nil
      }
    case _ => Nil
  },
    (ax:String) => (us:Subst) => ax match {
      case "+<= up" | "-<= up" | "<=+ down" | "<=- down" | "<= both" | "*<= up" | "<=* down" | "Div<= up" | "<=Div down" | "pow<= up" | "<=pow down" | "abs<= up" | "<=abs down" => us ++ RenUSubst(
        ("F_()".asTerm, FuncOf(Function(ubPrefix,None,Real,Real), us("f_()".asTerm))) ::
          ("G_()".asTerm, FuncOf(Function(ubPrefix,None,Real,Real), us("g_()".asTerm))) ::
          ("ff_()".asTerm, FuncOf(Function(lbPrefix,None,Real,Real), us("f_()".asTerm))) ::
          ("gg_()".asTerm, FuncOf(Function(lbPrefix,None,Real,Real), us("g_()".asTerm))) ::
          Nil)
      case _ => us
    }
  )

}