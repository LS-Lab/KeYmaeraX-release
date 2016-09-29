package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

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

  //Justifications for adding things to the context
  private val andLemma =
    proveBy(
      "((P_() <-> F_()) & (F_() -> (Q_() <-> G_()))) ->(P_() & Q_() <-> F_() & G_())".asFormula,prop)

  private val implyLemma =
    proveBy(
      "((P_() <-> F_()) & (F_() -> (Q_() <-> G_()))) ->(P_() -> Q_() <-> F_() -> G_())".asFormula,prop)

  private val orLemma =
    proveBy(
      "((P_() <-> F_()) & (!(F_()) -> (Q_() <-> G_()))) ->(P_() | Q_() <-> F_() | G_())".asFormula,prop)

  private val equivLemma =
    proveBy(
      "((P_() <-> F_()) & (Q_() <-> G_())) ->(P_() | Q_() <-> F_() | G_())".asFormula,prop)

  private val notLemma =
    proveBy(
      "(P_() <-> F_()) ->(!P_() <-> !F_())".asFormula,prop)

  /**
    * Recursive formula simplification under a context using chase, proving ctx |- f = f'
    * @param f formula to simplify
    * @param ctx context in which to simplify
    * @return
    */
  def formulaSimp(f:Formula, ctx:IndexedSeq[Formula] = IndexedSeq()) : Provable =
  {
    // todo: remove prop from short circuit branches
    // todo: Add derived axioms for missing cases of the chase simplification
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
          val nf = And(lf,rf)
          proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
            cut(Equiv(l,lf)) <(
              cut(Imply(lf,Equiv(r,rf))) <(
                useAt(andLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                  closeId,closeId
                  ),
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
          val nf = Imply(lf,rf)
          proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
            cut(Equiv(l,lf)) <(
              cut(Imply(lf,Equiv(r,rf))) <(
                useAt(implyLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                  closeId,closeId
                  ),
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
          val nf = Or(lf,rf)
          proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
            cut(Equiv(l,lf)) <(
              cut(Imply(Not(lf),Equiv(r,rf))) <(
                useAt(orLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                  closeId,closeId
                  ),
                hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & by(rpr)),
              hideR(SuccPos(0))& by(lpr)
              )
          )
        case Equiv(l, r) =>
          val lpr = formulaSimp(l, ctx)
          val lf = extract(lpr).asInstanceOf[Formula]
          val rpr = formulaSimp(r, ctx)
          val rf = extract(rpr).asInstanceOf[Formula]
          val nf = Equiv(lf,rf)
          proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
            cut(Equiv(l,lf)) <(
              cut(Equiv(r,rf)) <(
                useAt(equivLemma,PosInExpr(1::Nil))(SuccPos(0)) & andR(1) <(
                  closeId,closeId
                  ),
                hideL('Llast) & hideR(SuccPos(0)) & implyR(1) & by(rpr)),
              hideR(SuccPos(0))& by(lpr)
              )
          )
        case Not(u) =>
          val upr = formulaSimp(u, ctx)
          val uf = upr.conclusion.succ(0).sub(PosInExpr(1 :: Nil)).get.asInstanceOf[Formula]
          val nf = Not(uf)
          proveBy(Sequent(ctx, IndexedSeq(Equiv(f, nf))),
            cut(Equiv(u,uf)) < (
              useAt(notLemma,PosInExpr(1::Nil))(SuccPos(0)) & closeId,
              hideR(SuccPos(0))&by(upr)))
        case cf:ComparisonFormula =>
          val lpr = termSimp(cf.left)
          val rpr = termSimp(cf.right)
          val lt = extract(lpr).asInstanceOf[Term]
          val rt = extract(rpr).asInstanceOf[Term]
          val nf = cf.reapply(lt,rt)
          proveBy(Sequent(ctx, IndexedSeq(Equiv(cf, nf))),
            CEat(lpr)(SuccPosition(1,1::0::Nil))&
              CEat(rpr)(SuccPosition(1,1::1::Nil))&
              cohideR(SuccPos(0))& byUS(DerivedAxioms.equivReflexiveAxiom))
        case _ =>
          weaken(ctx)(DerivedAxioms.equivReflexiveAxiom.fact(
            USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), f) :: Nil)))
      }
    //println("Simplified: "+pf)
    //todo: Contextual chase
    //Chase simplification
    val cpr = chaseFor(3,3,e=>AxiomIndex.axiomsFor(e),(s,p)=>pr=>pr)(SuccPosition(1,1::Nil))(pf)
    //println("Final: "+cpr)
    //Simple example of contextual simplification
    val ff = extract(cpr).asInstanceOf[Formula]
    if (ctx.contains(ff))
    {
      proveBy(Sequent(ctx, IndexedSeq(Equiv(f, True))),
        cut(Equiv(f,ff)) <(
          equivR(1) < (closeT,closeId),
          hideR(SuccPos(0))& by(cpr)
          ))
    }
    else if (ctx.contains(Not(ff)))
    {
      proveBy(Sequent(ctx, IndexedSeq(Equiv(f, False))),
        cut(Equiv(f,ff)) <(
          prop,
          hideR(SuccPos(0))& by(cpr)
          ))
    }
    else
      cpr
  }


}
