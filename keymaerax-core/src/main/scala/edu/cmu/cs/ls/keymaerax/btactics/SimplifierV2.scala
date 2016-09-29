package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._

import scala.collection.immutable._

/**
  * Created by yongkiat on 9/29/16.
  */
object SimplifierV2 {

  /**
    * Returns the expression in expected position of |- t = t' or ctx |- f <-> f'
    * @param pr the provable from which to extract the expression
    * @return
    */
  private def extract(pr:Provable):Expression = {
    pr.conclusion.succ(0).sub(PosInExpr(1::Nil)).get
  }

  private def arithSimpAxioms(e:Expression): List[String] =
  {
    e match {
      case t:Term => t match{
        //todo: Need more simple arithmetic axioms in DerivedAxioms
        case Plus(_,_) => List("0+","+0","+ inverse")
        case Times(_,_) => List("0*","*0","* inverse")
        case _ => Nil
      }
      case _ => Nil
    }
  }

  /**
    * Recursive term simplification using chase, proving |- t = t'
    * @param t The term to be simplifed
    */
  def termSimp(t:Term): Provable =
  {
    //todo: This may need to be generalized to do allow term simplification under a context
    val init = DerivedAxioms.equalReflex.fact(USubst(SubstitutionPair(FuncOf(Function("s_",None,Unit,Real),Nothing), t)::Nil))
    val pf = t match {
      case bop: BinaryCompositeTerm =>
        val l = bop.left
        val r = bop.right
        val lpr = termSimp(l)
        val lt = extract(lpr).asInstanceOf[Term]
        val rpr = termSimp(r)
        val rt = extract(rpr).asInstanceOf[Term]
        val nt = bop.reapply(lt,rt)
        proveBy(Sequent(IndexedSeq(), IndexedSeq(Equal(t, nt))),
          CEat(lpr)(SuccPosition(1,1::0::Nil))&
            CEat(rpr)(SuccPosition(1,1::1::Nil))& by(init))
      case _ => init
    }
    //println("Simplified: "+pf)
    val fin = chaseFor(3,3,e=>arithSimpAxioms(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(pf)
    //println("Final: "+fin)
    fin
  }

  private def weaken(ctx:IndexedSeq[Formula]): ForwardTactic = pr => {
    val p = Provable.startProof(pr.conclusion.glue(Sequent(ctx, IndexedSeq())))
    proveBy(p,
      hideL('Llast)*ctx.length &
        by(pr))
  }

  /**
    * Recursive formula simplification under a context using chase, proving ctx |- f = f'
    * @param f formula to simplify
    * @param ctx context inwhich to simplify
    * @return
    */
  def formulaSimp(f:Formula, ctx:IndexedSeq[Formula] = IndexedSeq()) : Provable =
  {
    val pf =
      f match {
        case And(l, r) =>
          val lpr = formulaSimp(l, ctx)
          val lf = extract(lpr).asInstanceOf[Formula]
          //short circuit
          if (lf.equals(False))
          {
            return proveBy(Sequent(ctx,IndexedSeq(Equiv(f,False))),
              cut(Equiv(l,lf))<(
                prop,
                hideR(SuccPos(0))& by(lpr)))
          }
          //Use lf as part of context on the right
          val rpr = formulaSimp(r, ctx:+lf)
          val rf = extract(rpr).asInstanceOf[Formula]
          //todo: These should be caught by the chase below, but the axiom index doesn't have all the cases
          val nf = (lf,rf) match {
            case (True, _) => rf
            case (_, True) => lf
            case (_,False) => False
            case _ => And(lf,rf)
          }
          proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
            cut(Equiv(l,lf)) <(
              cut(Imply(lf,Equiv(r,rf))) <(
                prop,
                hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & by(rpr)),
              hideR(SuccPos(0))& by(lpr)
              )
          )
        case Imply(l, r) =>
          val lpr = formulaSimp(l, ctx)
          val lf = extract(lpr).asInstanceOf[Formula]
          //short circuit
          if (lf.equals(False))
          {
            return proveBy(Sequent(ctx,IndexedSeq(Equiv(f,True))),
              cut(Equiv(l,lf))<(
                prop,
                hideR(SuccPos(0))& by(lpr)))
          }
          //Use lf as part of context on the right
          val rpr = formulaSimp(r, ctx:+lf)
          val rf = extract(rpr).asInstanceOf[Formula]
          //todo: These should be caught by the chase below, but the axiom index doesn't have all the cases
          val nf = (lf,rf) match {
            case (True, _) => rf
            case (_, True) => True
            case (_,False) => Not(lf)
            case _ => Imply(lf,rf)
          }
          proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
            cut(Equiv(l,lf)) <(
              cut(Imply(lf,Equiv(r,rf))) <(
                prop,
                hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & by(rpr)),
              hideR(SuccPos(0))& by(lpr)
              )
          )
        case Or(l, r) =>
          val lpr = formulaSimp(l, ctx)
          val lf = extract(lpr).asInstanceOf[Formula]
          //short circuit
          if (lf.equals(True))
          {
            return proveBy(Sequent(ctx,IndexedSeq(Equiv(f,True))),
              cut(Equiv(l,lf))<(
                prop,
                hideR(SuccPos(0))& by(lpr)))
          }
          //Use lf as part of context on the right
          val rpr = formulaSimp(r, ctx:+Not(lf))
          val rf = extract(rpr).asInstanceOf[Formula]
          //todo: These should be caught by the chase below, but the axiom index doesn't have all the cases
          val nf = (lf,rf) match {
            case (False, _) => rf
            case (_, True) => True
            case (_,False) => lf
            case _ => Or(lf,rf)
          }
          proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
            cut(Equiv(l,lf)) <(
              cut(Imply(Not(lf),Equiv(r,rf))) <(
                prop,
                hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & by(rpr)),
              hideR(SuccPos(0))& by(lpr)
              )
          )
        case Equiv(l, r) => ???
        case Not(u) =>
          val upr = formulaSimp(u, ctx)
          val uf = upr.conclusion.succ(0).sub(PosInExpr(1 :: Nil)).get.asInstanceOf[Formula]
          val nf = uf match {
            case True => False
            case False => True
            case _ => Not(uf)
          }
          proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
            cut(Equiv(u,uf)) < (
              prop,
              hideR(SuccPos(0))&by(upr)))
        case cf:ComparisonFormula =>
          val lpr = termSimp(cf.left)
          val rpr = termSimp(cf.right)
          val lt = extract(lpr).asInstanceOf[Term]
          val rt = extract(rpr).asInstanceOf[Term]
          val nf = cf.reapply(lt,rt)
          proveBy(Sequent(ctx, IndexedSeq(Equiv(cf, nf))),
            CEat(lpr)(SuccPosition(1,1::0::Nil))&
              CEat(rpr)(SuccPosition(1,1::1::Nil))& prop)
        case _ =>
          //Try to prove that the context already implies the formula
          val pr = TactixLibrary.proveBy(Sequent(ctx, IndexedSeq(Equiv(f, True))), prop)
          if (pr.isProved)
            pr
          //otherwise, try to prove that it is inconsistent
          else {
            val prf = TactixLibrary.proveBy(Sequent(ctx, IndexedSeq(Equiv(f, False))), prop)
            if (prf.isProved)
              prf
            else
              weaken(ctx)(DerivedAxioms.equivReflexiveAxiom.fact(
                USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), f) :: Nil)))
          }
      }
    //println("Simplified: "+pf)
    //todo: Contextual chase
    val fin = chaseFor(3,3,e=>AxiomIndex.axiomsFor(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(pf)
    //println("Final: "+fin)
    fin
  }


}
