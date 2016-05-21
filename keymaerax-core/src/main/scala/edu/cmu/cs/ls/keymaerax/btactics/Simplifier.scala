package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.AxiomIndex.AxiomIndex
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._

import scala.language.postfixOps


/**
  * Created by bbohrer on 5/21/16.
  */
object Simplifier {
  trait Simplification extends (Term => Option[(Term, BelleExpr)]){}

  def trav(simps:List[Simplification]) = new ExpressionTraversalFunction {
    var result:Option[(PosInExpr, Term, BelleExpr)] = None
    override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
      simps.find({case simp => simp(e).isDefined}) match {
        case Some(simp) =>
          simp(e) match {
            case Some((newTerm, belle)) =>
              result = Some((p, newTerm, belle))
              Left(Some(ExpressionTraversal.stop))
            case None => throw new ProverException("Bad pattern-match in Simplifier.scala")
          }
        case None => Left(None)
      }
    }
  }
  def simp(simps:List[Simplification], e:Formula):Option[(PosInExpr, Term, BelleExpr)] = {
    val t = trav(simps)
    ExpressionTraversal.traverse(t, e)
    t.result
  }

  def simp(simps:List[Simplification], e:Term):Option[(PosInExpr, Term, BelleExpr)] = {
    val t = trav(simps)
    ExpressionTraversal.traverse(t, e)
    t.result
  }

  def simp(simps:List[Simplification], e:Program):Option[(PosInExpr, Term, BelleExpr)] = {
    val t = trav(simps)
    ExpressionTraversal.traverse(t, e)
    t.result
  }

  def makeCE(fml:Formula, opt:Option[(PosInExpr, Term, BelleExpr)]):BelleExpr = {
    opt match {
      case Some((pos, t2, e)) =>
        val (ctx, t1:Term) = fml.at(pos)
        val eqProof = TactixLibrary.proveBy(Equal(t1, t2), e)
        HilbertCalculus.useAt(HilbertCalculus.CE(ctx)(eqProof), PosInExpr(0::Nil))
      case None => TactixLibrary.nil
    }
  }

  def simp(simps:List[Simplification]):DependentPositionTactic = "diffWeaken" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(fml : Formula) => makeCE(fml, simp(simps, fml))
    /*case Some(fml : Term)    => makeCE(fml, simp(simps, fml))
    case Some(fml : Program) => makeCE(simp(simps, fml))*/
    case None => TactixLibrary.nil
  })
}

