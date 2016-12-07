/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, PosInExpr}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.printIndexed
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Conditional congruence reasoning for ACAS X to use conditional equivalence lemmas
 * on the implicit region safety theorems to obtain the explicit region safety corollaries.
 * @author Stefan Mitsch
 * @author Andre Platzer
 */
object CondCongruence {

  /**
   * Corollary proved by conditional congruence reasoning.
   * ACAS X proof embedding conditional equivalence of implicit region and explicit region
   * into the safety proof for the implicit regions
   * to obtain a safety proof for the explicit regions.
   * @param implicitExplicit conditional equivalence result for implicit and explicit regions.
   * @param acasximplicitP safe hybrid systems model with provably safe implicit regions
   * @param acasxexplicit conjectured hybrid systems model with explicit regions
   * @param ucLoLemma additional lemma proving the extra liveness condition u from the invariant: A&W(w)&Ci->u
   * @param done what to call at arithmetic leaves
   * @return a proof of acasxexplicit as constructed out of the other ingredients.
   * @author Andre Platzer
   */
  def acasXcongruence(implicitExplicit: ProvableSig, acasximplicitP: ProvableSig, ucLoLemma: ProvableSig, acasxexplicit: Formula, done: BelleExpr = close): ProvableSig = {
    // input shape requirements
    println("implicit-explicit lemma subgoals: " + implicitExplicit.subgoals)
    require(implicitExplicit.conclusion.ante.isEmpty, "Equivalence of implicit and explicit should be proved")
    require(implicitExplicit.conclusion.succ.length == 1, "Equivalence proof should have exactly one conclusion")
    val equivalence = implicitExplicit.conclusion.succ.head
    // extract subformulas A()&W(w) -> (Ce(...)<->Ci(...))
    val Imply(And(a,w), Equiv(e,i)) = equivalence

    require(acasximplicitP.conclusion.ante.isEmpty, "Implicit safety should be proved")
    require(acasximplicitP.conclusion.succ.length == 1, "Implicit safety proof should have exactly one conclusion")
    val acasximplicit = acasximplicitP.conclusion.succ.head
    acasximplicit match {
      case Imply(And(aa, And(ww, c)), Box(Loop(_), And(_, c2))) if aa == a && ww == w && c == i && c2 == i =>
      case _ => throw new IllegalArgumentException("Unexpected input shape of implicit file\nFound:    " + acasximplicit
        + "\nExpected: " + Imply(And(a, And(w, i)), Context(Box(
        """
          |{   {
          |      { ?true; ++
          |        {dhf :=*; {w:=-1; ++ w:=1;}
          |         ?⎵;
          |        }}
          |        ao :=*;
          |      }
          |      {r' = -rv, h' = -dhd, dhd' = ao & (w * dhd >= w * dhf | w * ao >= a)}
          |   }*
        """.stripMargin.asProgram, And("abs(r)>rp|abs(h)>hp".asFormula, i))) (i)))

    }
    val Imply(And(_, And(_, _)), Box(Loop(_), And(u, _))) = acasximplicit

    acasxexplicit match {
      case Imply(And(aa, And(ww, c)), Box(Loop(_), And(_, c2))) if aa == a && ww == w && c == e && c2 == e =>
      case _ => throw new IllegalArgumentException("Unexpected input shape of explicit file\nFound:    " + acasxexplicit
        + "\nExpected: " + Imply(And(a, And(w, e)), Context(Box(
        """
          |{   {
          |      { ?true; ++
          |        {dhf :=*; {w:=-1; ++ w:=1;}
          |         ?⎵;
          |        }}
          |        ao :=*;
          |      }
          |      {r' = -rv, h' = -dhd, dhd' = ao & (w * dhd >= w * dhf | w * ao >= a)}
          |   }*
        """.stripMargin.asProgram, And("abs(r)>rp|abs(h)>hp".asFormula, e))) (e))
      )
    }

    // reading off more minor lemmas from equivalence lemma

    //@note same proof of seqEquivalence as in "derive sequent version of conditional equivalence"
    // A() & W(w) |- Ce<->ci
    val seqEquivalence = (ProvableSig.startProof(Sequent(IndexedSeq(a, w), IndexedSeq(Equiv(e,i))))
    (Cut(equivalence), 0)
    // right branch reduces to the proof of "equivalence"
    (CoHideRight(SuccPos(1)), 1)
    // left branch follows from "equivalence"
    (ImplyLeft(AntePos(2)), 0)
    // third branch e<->i |- e<->i
    (Close(AntePos(2), SuccPos(0)), 2)
    // second branch a,w |- e<->i, a&w
    (AndRight(SuccPos(1)), 0)
    // second-right branch a,w |- e<->i, w
    (Close(AntePos(1), SuccPos(1)), 2)
    // second-left branch a,w |- e<->i, a
    (Close(AntePos(0), SuccPos(1)), 0)
    // drag&drop proof
    (implicitExplicit, 0) )
    assert(seqEquivalence.subgoals == implicitExplicit.subgoals)
    assert(implicitExplicit.isProved == seqEquivalence.isProved, "proved iff equivalence is proved")
    // used to produce equivalent logically reshuffled version of equivalence lemma: (A()&W()->(Ce()<->Ci())) -> ((W()->A()->u()&Ci()) <-> (W()->A()->u()&Ce()))
    val shuffle = TactixLibrary.proveBy("(A()&W()->(Ce()<->Ci())) -> ((W()->A()->u()&Ci()) <-> (W()->A()->u()&Ce()))".asFormula, prop)
    assert(shuffle.isProved)
    // equivalence used in the postcondition
    // (W(w)->A()->u&Ci(w,dhf)) <-> (W(w)->A()->u&Ce(w,dhf))
    val postEquivalence = TactixLibrary.proveBy(
      Equiv(Imply(w,Imply(a, And(u, i))),
        Imply(w,Imply(a, And(u, e))))
      , useAt(shuffle, PosInExpr(1::Nil))(1)
        & by(implicitExplicit))
    assert(postEquivalence.subgoals == implicitExplicit.subgoals)

    //@note _0 naming variations would be introduced in ordinary induction. Avoid renaming by global loop invariants instead, even if that adds a number of repeated proof steps.
    //@note The unnecessary flexibility coming from these cause considerable duplication in the subsequent proof, because the same thing is proved in different places for w and w0 which end up being the same here.
    val w0 = w // "W(w_0)".asFormula
    val i0 = i // "Ci(w_0,dhf_0)".asFormula
    val e0 = e // "Ce(w_0,dhf_0)".asFormula
    val u0 = u // "(h_0 < -hp | h_0 > hp | r_0 < -rp | r_0> rp)".asFormula

    // (A()&W(w) -> Ce(w,dhf))  <->  (A()&W(w) -> Ci(w,dhf))
    val distEquivalence = TactixLibrary.proveBy(Sequent(IndexedSeq(), IndexedSeq(Equiv(Imply(And(a,w), e), Imply(And(a,w),i)))),
      useAt("-> distributes over <->", PosInExpr(1::Nil))(1)
        & by(implicitExplicit))
    assert(distEquivalence.subgoals == implicitExplicit.subgoals)
    assert(distEquivalence.isProved == implicitExplicit.isProved, "proved if equivalence proved")
    val shuffle2 = TactixLibrary.proveBy("(A()&W()->(Ce()<->Ci())) -> ((A()&W() -> Ce() -> q()) <-> (A()&W() -> Ci() -> q()))".asFormula, prop)
    assert(shuffle2.isProved)
    // (A()&W(w_0) -> Ce(w_0,dhf_0) -> q())  <->  (A()&W(w_0) -> Ci(w_0,dhf_0) -> q())
    val distEquivImpl = TactixLibrary.proveBy(Sequent(IndexedSeq(), IndexedSeq(Equiv(
      Imply(And(a,w0), Imply(e0, "q()".asFormula)),
      Imply(And(a,w0), Imply(i0, "q()".asFormula))))),
      // //useAt("-> distributes over <->", PosInExpr(1::Nil))(1))
      useAt(shuffle2, PosInExpr(1::Nil))(1)
        & byUS(implicitExplicit))
    assert(distEquivImpl.subgoals == implicitExplicit.subgoals)
    println("distEquivImpl " + distEquivImpl)


    // begin actual proof

    // tactic for induction step for W ...
    val invariantWT =
    // could also just always generalize(w0)
    // this is a more efficient version
    //@note could have handled 2*composeb(1) at once
    //@note useing W(w_0) instead of W(w) or use post-postcondition
      composeb(1) & generalize(w0)(1) & Idioms.<(
        /*use*/ composeb(1) & useAt("V[:*] vacuous assign nondet")(1, 1::Nil) &
          choiceb(1) & andR(1) & Idioms.<(
          sublabel("& left") & testb(1) & implyR(1) & closeId & done
          ,
          sublabel("& right") &
            composeb(1) & composeb(1, 1::Nil) & generalize(w0)(1) & Idioms.<(
            /*use*/ useAt("V[:*] vacuous assign nondet")(1) & closeId,
            /*show*/ generalize(w0)(1) & Idioms.<(
              /*use*/ sublabel("W arith") & printIndexed("W arith") & cohide(1) & master() & done,
              /*show*/ printIndexed("W gen V 2") & V(1) & closeId & done
            )
          )
        )
        ,
        /*show*/ printIndexed("W gen V 1") & V(1) & closeId & done
      )

    // W is invariant proof for both implicit and explicit models. Same tactic above.
    val invariantWe = TactixLibrary.proveBy(
      Sequent(IndexedSeq(w), IndexedSeq(Box(
        acasxexplicit match {case Imply(And(_, And(_, _)), Box(Loop(body), And(_, _))) => body}, w)))
      ,
      invariantWT)

    // main proof

    val proof = TactixLibrary.proveBy(acasxexplicit,
      implyR(1) & andL(-1) &
        // augment postcondition with A() ->
        postCut(a)(1) & andR(1) & Idioms.<(
        // augmented postcondition with A() ->
        /*use*/ label("") & printIndexed("true induction need") &
          // augment postcondition with W(w) ->
          postCut(w)(1) & andR(1) & Idioms.<(
          // augmented postcondition with W(w) -> A() ->
          /*use*/ sublabel("A()&W(w) augmented") & DebuggingTactics.assert(And(w,e), "W&Ce")(-2) & andL(-2) & printIndexed("inductive use of A&W") &
            // replace explicit Ce in precondition with implicit Ci
            cutL(i)(-3) & Idioms.<(
            /*use*/ sublabel("Ce~>Ci reduction") & label("Ce~>Ci reduction") & printIndexed("Ce~>Ci reduction") &
              // replace explicit Ce in postcondition with implicit Ci
              CEat(postEquivalence)(1, 1::Nil)//CE(postEquivalence)(1, 1::Nil)
              & printIndexed("Ce~>Ci reduced in postcondition")

              // main part of the proof
              // working toward replacing Ce by Ci in the dynamics
              & printIndexed("unpack and repack to replace test") &
              /*loop(And(w,And(u, i)))(1)*/
              // loop invariant A() & ( W(w) & (u&Ci) )
              DLBySubst.loop(And(a,And(w,And(u, i))), pre=skip)(1)
              & sublabel("loop induction")
              & Idioms.<(
              /*init*/ sublabel("W&u&Ci init") & printIndexed("W&u&Ci init") & andR(1) & Idioms.<(prop & done, andR(1) & Idioms.<(closeId & done, andR(1) & Idioms.<(
                label("arith") /*& done*/
                  & printIndexed("A&W(w)&Ci->u")
                  & printIndexed("Using ucLoLemma")
                  & assertE(ucLoLemma.conclusion.succ.head, "ucLoLemma not applicable, have unexpected goal")(1) & by(ucLoLemma)
                , close(-3,1))))
              ,

              /*use case*/ sublabel("final use") & printIndexed("final use") & (andL('L)*) & implyR('R)*2
                & andR('R) & onAll(closeId) & done
              ,

              /*step*/ sublabel("W&u&Ci step") & printIndexed("W&u&Ci step") & // hide(And(w,And(u,i)))(-4) & hide(i)(-3) & hide(w)(-2) &
                andL('L, And(a,And(w,And(u, i)))) & assertE(a, "A()")(-1) &
                boxAnd(1) & andR(1) & Idioms.<(
                // A() invariant by V
                V(1) & closeId
                ,
                // implyR(1) &
                boxAnd(1) & andR(1) & Idioms.<(
                  // W(w) invariant as above
                  printIndexed("W invariant again") &
                    andL('L, And(w,And(u, i))) & andL('L, And(u, i))
                    & hideL('L, i) & hideL('L, u) & (hideL('L, a)*) & // a appears duplicated
                    by(invariantWe)
                  ,
                  // u&Ce invariant
                  // by unpacking, replacing Ce with Ci, repacking, and using the lemma
                  // unpack prefix before ?Ce in dynamics
                  composeb(1) & composeb(1) & choiceb(1)
                    //& useAt("[;] compose", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil))  // gather
                    & composeb(1, 1::Nil) & composeb(1, 1::1::Nil)
                    & printIndexed("cutting explicit dynamics away")
                    // replace explicit condition in context by implicit Ci condition, essentially by advanced CMon++
                    & cutAt(i0)(1, 1::1::1::0::0::Nil) & printIndexed("cuttedAt") & Idioms.<(
                    /*use*/ sublabel("use patch") & printIndexed("use patch")
                      // repacking
                      & useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::Nil) & useAt("[;] compose", PosInExpr(1::Nil))(1, 1::Nil)
                      //& useAt("[;] compose", PosInExpr(0::Nil))(SuccPosition(0, 1::Nil))// ungather
                      // repack
                      & useAt("[++] choice", PosInExpr(1::Nil))(1) & useAt("[;] compose", PosInExpr(1::Nil))(1) & useAt("[;] compose", PosInExpr(1::Nil))(1)
                      & label("use patch") & printIndexed("used patch")
                      // by unrolling implicit once
                      //@todo rename acasximplicit to w_0 names or vice versa ....
                      & cut(acasximplicit.asInstanceOf[Imply].right) & Idioms.<(
                      /*use*/ sublabel("by implicit") & useAt("[*] approx")('Llast) & closeId & done,
                      /*show*/ sublabel("show implicit applicable") &
                          hide(1) &
                          cut(acasximplicit) & Idioms.<(
                          /*use*/ sublabel("show lemma assumptions") & label("") & printIndexed("show lemma assumptions") &
                              implyL('L, acasximplicit) & Idioms.<(
                              hide(1) &
                                label("step 1") &
                                // prove A()&(W(w)&Ci(w,dhf))
                                andR(1) & Idioms.<(
                                label("A id") & closeId
                                ,
                                // split W(w)&u&Ci finally
                                label("step W(w)&Ci") & printIndexed("step W(w)&Ci") &
                                  andL('L, And(w,And(u,i))) & andL('L, And(u,i)) &
                                  andR(1) & Idioms.<(
                                  label("W(w) id") & closeId // (-2,1)
                                  ,
                                  label("Ci id") & closeId //(-4,1)
                                  /*andR(1) & (
                                    label("arithmetic")
                                    ,
                                    label("Ci id") & closeId //(-4,1)
                                    )
                                    */
                                  )
                                )
                              ,
                              label("looked up") & closeId)
                          ,
                          /*show*/ cohide('R, acasximplicit) & sublabel("lookup lemma") & label("") & by(acasximplicitP)
                        )
                        // show implicit applicable

                    ) // use patch
                    ,

                    /*show*/ sublabel("show patch") & printIndexed("showing patch")
                      & useAt("-> distributes over &", PosInExpr(0::Nil))(1)
                      & andR(1) & Idioms.<(
                      // left branch is unchanged
                      sublabel("cutAt no change on left") & implyR(1) & andL(-4) & closeId
                      ,
                      // right branch replaced implicit with explicit conditionally
                      sublabel("CMon++")
                        & printIndexed("CMon++")
                        & useAt("& commute")(1, 0::Nil)
                        & printIndexed("& commuted")
                        & useAt("-> weaken", PosInExpr(1::Nil))(1)
                        & printIndexed("-> weakened")
                        & label("CMon") & printIndexed("CMon")
                        & sublabel("-> weakened")
                        // the following is like CMon(PosInExpr(1::1::1::0::0::Nil)) except with context kept around
                        & implyR(1)
                        & printIndexed("->R ed")
                        /*
                        & (choiceb(1, 1::Nil) & choiceb(-3, 1::Nil))
                        & (useAt("[:=] assign")(1, 1::0::Nil) & useAt("[:=] assign")(-3, 1::0::Nil))
                        & (useAt("[:=] assign")(1, 1::1::Nil) & useAt("[:=] assign")(-3, 1::1::Nil))
                        & (randomb(1) & randomb(-3))
                        */
                        // gather outer [dhf:=*;][w:=-1;++w:=1;] boxes to single [;]
                        & sublabel("gathering") & printIndexed("gathering")
                        // A(), W(w)&u&Ci((w,dhf)), [dhf:=*;][w:=-1;++w:=1;][?Ci((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))  ==>  [dhf:=*;][w:=-1;++w:=1;][?Ce((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))
                        // reverse application to repack prefix
                        & useAt("[;] compose", PosInExpr(1::Nil))(1)
                        & useAt("[;] compose", PosInExpr(1::Nil))(-4)
                        & printIndexed("gathered")
                        // A(), W(w)&u&Ci((w,dhf)), [dhf:=*;{w:=-1;++w:=1;}][?Ci((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))  ==>  [dhf:=*;{w:=-1;++w:=1;}][?Ce((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))
                        & sublabel("postCut A()&W(w0)") & printIndexed("postCut A()&W(w0)")
                        // augment postcondition with A()&W(w) ->
                        & postCut(And(a,w0))(1) & andR(1) & Idioms.<(
                        /*use*/ sublabel("generalized A()&W(w0)->post")
                          & testb(1, 1::1::Nil)
                          & printIndexed("do use dist equiv impl")
                          & assertE(And(a,w0), "do use dist equiv form")(1, 1::0::Nil)
                          & assertE(e0, "do use dist equiv form")(1, 1::1::0::Nil)
                          & assertE("dhf:=*;{w:=-1;++w:=1;}".asProgram, "do use dist equiv form")(1, 0::Nil)
                          & assertE("ao:=*;".asProgram, "do use dist equiv form")(1, 1::1::1::0::Nil)
                          // [dhf:=*;{w:=-1;++w:=1;}]__(A()&W(w)->Ce(w,dhf) -> [ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci))__
                          // __(A()&W(w_0) -> Ce(w_0,dhf_0) -> q())__  <->  (A()&W(w_0) -> Ci(w_0,dhf_0) -> q())
                          // use distributed version of equivalence
                          & useAt(distEquivImpl, PosInExpr(0::Nil))(1, 1::Nil)
                          & sublabel("dist equiv impl")
                          & printIndexed("used dist equiv impl")
                          & assertE(And(a,w0), "used dist equiv form")(1, 1::0::Nil)
                          & assertE(i0, "used dist equiv form")(1, 1::1::0::Nil)
                          & assertE("dhf:=*;{w:=-1;++w:=1;}".asProgram, "used dist equiv form")(1, 0::Nil)
                          & assertE("ao:=*;".asProgram, "used dist equiv form")(1, 1::1::1::0::Nil)
                          //                      & (if (distEquivImpl.isProved) {
                          //                      assertE("dhf_0:=*;{w_0:=-1;++w_0:=1;}".asProgram, "used dist equiv form")(1, 0 :: Nil) &
                          //                        assertE ("ao:=*;".asProgram, "used dist equiv form")(1, 1::1::1::0::Nil)
                          //                    } else {
                          //                    //  println("WARN: unproved distEquivImpl, so proof goals will remain around");
                          //                      skip
                          //                    })
                          // repacking replaced test ?Ci
                          & useAt("[?] test", PosInExpr(1::Nil))(1, 1::1::Nil)
                          & printIndexed("repacked test")
                          // drop a&w implication from postcondition again
                          //& useAt("K modal modus ponens", PosInExpr(0::Nil))(1) & implyR(1) & hide(-4)
                          & sublabel("[] post weaken")
                          & printIndexed("do [] post weaken")
                          & assertE(And(a,w0), "post weaken form")(1, 1::0::Nil)
                          & assertE(Test(i0), "post weaken form")(1, 1::1::0::Nil)
                          & useAt("[] post weaken", PosInExpr(1::Nil))(1) //& useAt("[] post weaken")(1, /*Nil*/1::1::1::Nil)
                          & printIndexed("did [] post weaken")
                          & closeId
                        // successfully closes
                        // generalized A()&W(w0)->post
                        ,

                        /*show*/ sublabel("generalize post A()&W(w0)")
                          & hide(-4) & hideL('L, And(w0,And(u0,i0))) & sublabel("chasing") & chase(1)
                          & allR(1) // equivalent:  HilbertCalculus.vacuousAll(1)
                          & sublabel("gen by arith") & printIndexed("gen by arith")
                          & andR(1) & Idioms.<(
                          andR(1) & Idioms.<(
                            closeId
                            ,
                            done // QE
                          )
                          ,
                          andR(1) & Idioms.<(
                            closeId
                            ,
                            done //QE
                          )
                        )
                        // generalize post A()&W(w0)
                      )  // postCut(And(a,w0))
                    )  // andR within show patch
                    // show patch
                  )  // cutAt(i0)
                  )  // u&Ce invariant
                )
                // W(w)&Ci step
            ) // ind(And(a,And(w,And(u, i))))
            ,
            /*show*/ hide(1) & label("by seq-equiv") & equivifyR(1) & by(seqEquivalence) & done
          ) // cutL(i)(-3)
          ,
          /*show*/ label("") & printIndexed("w=-1 | w=1") & DebuggingTactics.assert(And(w,e), "W&Ce")(-2) & andL(-2) &
            // prove that W(w) === w=-1 | w=1 is a loop invariant
            //loop(w)(1)
            loop(w)(1) & Idioms.<(
            /*base*/ sublabel("W(w) init") & closeId & done
            ,
            /*use*/ sublabel("W(w) loop use") & closeId & done
            ,
            /*step*/ sublabel("W(w) step") &
              /* rebuild and hide a */
              (("ANON" by {(seq: Sequent) =>
                  DebuggingTactics.assertAt((_: Expression) => "Stopping repeat", (e: Expression) => e != a)(AntePos(seq.ante.length-1)) &
                  andLi(AntePos(seq.ante.length-2), AntePos(seq.ante.length-1))})*) &
              hideL('Llast) & printIndexed("step w=-1 | w=1") & by(invariantWe)
          )
          // end show postCut(w)
        )
        ,
        // A() invariant by V
        /*show*/ sublabel("A() vacuous") & printIndexed("vacuous global assumptions") & V(1) & closeId
      ) // postCut(a)
    )

    proof
  }


  /**
   * ACAS X proof embedding conditional equivalence of implicit and explicit into safety proof of implicit regions
   * to form a safety proof of explicit regions.
   * @param implicitExplicit conditional equivalence result for implicit, explicit regions
   * @param acasximplicitP safe hybrid systems model with implicit regions
   * @param acasxexplicit conjectured hybrid systems model with explicit regions
   * @param done what to call at arithmetic leaves
   * @return a proof of acasxexplicit as constructed out of the other ingredients.
   * @author Andre Platzer
   */
  def acasXTLcongruence(implicitExplicit: ProvableSig, acasximplicitP: ProvableSig, ucLoLemma: ProvableSig, acasxexplicit: Formula, done: BelleExpr = close): ProvableSig = {
    //@todo compiles but not yet ported
    println("implicit-explicit lemma subgoals: " + implicitExplicit.subgoals)
    require(implicitExplicit.conclusion.ante.isEmpty, "Equivalence of implicit and explicit should be proved without assumptions")
    require(implicitExplicit.conclusion.succ.length == 1, "Equivalence proof should have exactly one conclusion")
    val equivalence = implicitExplicit.conclusion.succ.head
    // extract subformulas A()&W(w) -> (Ce(...)<->Ci(...))
    val Imply(And(a,w), Equiv(e,i)) = equivalence

    require(acasximplicitP.conclusion.ante.isEmpty, "Implicit safety should be proved without assumptions")
    require(acasximplicitP.conclusion.succ.length == 1, "Implicit safety proof should have exactly one conclusion")
    val acasximplicit = acasximplicitP.conclusion.succ.head
    acasximplicit match {
      case Imply(And(aa, And(ww, c)), Box(Loop(_), And(_, And(_, c2)))) if aa == a && ww == w && c == i && c2 == i =>
      case _ => throw new IllegalArgumentException("Unexpected input shape of implicit file\nFound:    " + acasximplicit
        + "\nExpected: " + Imply(And(a, And(w, i)), Context(Box(
        """
          |{   {
          |      { ?true; ++
          |        {dhf :=*; {w:=-1; ++ w:=1;}
          |         ?⎵;
          |        }}
          |        ao :=*;
          |      }
          |      {r' = -rv, dhd' = ao, h' = -dhd & (w * dhd >= w * dhf | w * ao >= a)}
          |   }*
        """.stripMargin.asProgram, And("abs(r)>rp|abs(h)>hp".asFormula, i))) (i)))

    }
    val Imply(And(_, And(_, _)), Box(Loop(_), And(u1, And(u2, _)))) = acasximplicit

    acasxexplicit match {
      case Imply(And(aa, And(ww, c)), Box(Loop(_), And(_, And(_, c2)))) if aa == a && ww == w && c == e && c2 == e =>
      case _ => throw new IllegalArgumentException("Unexpected input shape of explicit file\nFound:    " + acasxexplicit
        + "\nExpected: " + Imply(And(a, And(w, e)), Context(Box(
        """
          |{   {
          |      { ?true; ++
          |        {dhf :=*; {w:=-1; ++ w:=1;}
          |         ?⎵;
          |        }}
          |        ao :=*;
          |      }
          |      {r' = -rv, dhd' = ao, h' = -dhd & (w * dhd >= w * dhf | w * ao >= a)}
          |   }*
        """.stripMargin.asProgram, And("abs(r)>rp|abs(h)>hp".asFormula, e))) (e))
      )
    }

    // read off more lemmas from equivalence

    //@note same proof of seqEquivalence as in "derive sequent version of conditional equivalence"
    val seqEquivalence = (ProvableSig.startProof(Sequent(IndexedSeq(a, w), IndexedSeq(Equiv(e,i))))
    (Cut(equivalence), 0)
    // right branch reduces to the proof of "equivalence"
    (CoHideRight(SuccPos(1)), 1)
    // left branch follows from "equivalence"
    (ImplyLeft(AntePos(2)), 0)
    // third branch e<->i |- e<->i
    (Close(AntePos(2), SuccPos(0)), 2)
    // second branch a,w |- e<->i, a&w
    (AndRight(SuccPos(1)), 0)
    // second-right branch a,w |- e<->i, w
    (Close(AntePos(1), SuccPos(1)), 2)
    // second-left branch a,w |- e<->i, a
    (Close(AntePos(0), SuccPos(1)), 0)
    // drag&drop proof
    (implicitExplicit, 0) )
    assert(seqEquivalence.subgoals == implicitExplicit.subgoals)
    val shuffle = TactixLibrary.proveBy("(A()&W()->(Ce()<->Ci())) -> ((W()->A()->u1()&u2()&Ci()) <-> (W()->A()->u1()&u2()&Ce()))".asFormula, prop)
    assert(shuffle.isProved)
    // (W(w)->A->u&Ci(w,dhf)) <-> (W(w)->A->u&Ce(w,dhf))
    val postEquivalence = TactixLibrary.proveBy(
      Equiv(Imply(w,Imply(a, And(u1, And(u2, i)))),
        Imply(w,Imply(a, And(u1, And(u2, e)))))
      , useAt(shuffle, PosInExpr(1::Nil))(1)
        & by(implicitExplicit))
    assert(postEquivalence.subgoals == implicitExplicit.subgoals)

    //@note _0 variations in induction :-/
    val w0 = w // "W(w_0)".asFormula
    val i0 = i // "Ci(w_0,dhf_0)".asFormula
    val e0 = e // "Ce(w_0,dhf_0)".asFormula
    val u0 = u1 // "(h_0 < -hp | h_0 > hp | r_0 < -rp | r_0> rp)".asFormula

    // (A()&W(w) -> Ce(w,dhf))  <->  (A()&W(w) -> Ci(w,dhf))
    val distEquivalence = TactixLibrary.proveBy(Sequent(IndexedSeq(), IndexedSeq(Equiv(Imply(And(a,w), e), Imply(And(a,w),i)))),
      useAt("-> distributes over <->", PosInExpr(1::Nil))(1)
        & by(implicitExplicit))
    assert(distEquivalence.subgoals == implicitExplicit.subgoals)
    val shuffle2 = TactixLibrary.proveBy("(A()&W()->(Ce()<->Ci())) -> ((A()&W() -> Ce() -> q()) <-> (A()&W() -> Ci() -> q()))".asFormula, prop)
    assert(shuffle2.isProved)
    // (A()&W(w_0) -> Ce(w_0,dhf_0) -> q())  <->  (A()&W(w_0) -> Ci(w_0,dhf_0) -> q())
    val distEquivImpl = TactixLibrary.proveBy(Sequent(IndexedSeq(), IndexedSeq(Equiv(
      Imply(And(a,w0), Imply(e0, "q()".asFormula)),
      Imply(And(a,w0), Imply(i0, "q()".asFormula))))),
      // //useAt("-> distributes over <->", PosInExpr(1::Nil))(1))
      useAt(shuffle2, PosInExpr(1::Nil))(1)
        & byUS(implicitExplicit))
    assert(distEquivImpl.subgoals == implicitExplicit.subgoals)
    println("distEquivImpl " + distEquivImpl)

    // begin actual proof

    val invariantWT =
    // could also just always generalize(w0)
    // this is a more efficient version
    //@note could have handled 2*composeb(1) at once
    //@note useing W(w_0) instead of W(w) or use post-postcondition
      composeb(1) & generalize(w0)(1) & Idioms.<(
        /*show*/ printIndexed("W gen DW") & DW(1) & implyR(1) & andL(-2) & andL(-1) & andR(1) & closeId,
        /*use*/ composeb(1) & useAt("V[:*] vacuous assign nondet")(1, 1::Nil) &
          choiceb(1) & andR(1) & Idioms.<(
          sublabel("& left") & testb(1) & implyR(1) & closeId
          ,
          sublabel("& right") &
            composeb(1) & composeb(1, 1::Nil) & composeb(1, 1::1::Nil) & generalize(w0)(1) & Idioms.<(
            /*use*/ assignb(1) & andL(-1) & andR(1) & Idioms.<(closeId, QE),
            /*show*/ generalize(w0)(1) & Idioms.<(
              /*show*/ generalize(w0)(1) & Idioms.<(
                /*show*/ sublabel("W arith") & andL(-1) & hideL(-1) & composeb(1) &
                  printIndexed("W arith") & choiceb(1) & useAt("[:=] assign")(1, 0::Nil) & useAt("[:=] assign")(1, 1::Nil) &
                  useAt("[?] test")(1, 0::Nil) & useAt("[?] test")(1, 1::Nil) & QE,
                /*use*/ printIndexed("W gen V 2") & V(1) & closeId
              ),
              /*use*/ printIndexed("W gen V 1") & V(1) & closeId
            )
          )
          )
      )

    // W is invariant proof for both implicit and explicit models. Same tactic above.
    val invariantWe = TactixLibrary.proveBy(
      Sequent(IndexedSeq(w), IndexedSeq(Box(acasxexplicit match {case Imply(_, Box(Loop(body), _)) => body}, w))),
      invariantWT)

    assert(invariantWe.isProved)

    val proof = TactixLibrary.proveBy(acasxexplicit,
      implyR(1) & andL(-1) &
        postCut(a)(1) & Idioms.<(
        /*show*/ sublabel("A() vacuous") & printIndexed("vacuous global assumptions") & V(1) & close(-1, 1),

        /*use*/ label("") & printIndexed("true induction need") &

          postCut(w)(1) & Idioms.<(
          /*show*/ label("") & printIndexed("w=-1 | w=1") & DebuggingTactics.assert(And(w,e), "W&Ce")(-2) & andL(-2) &
            //loop(w)(1)
            loop(w)(1) & Idioms.<(
            /*init*/ sublabel("W(w) init") & closeId,

            /*step*/ sublabel("W(w) step") & //hide(w)(-4) & hide(w)(-2) &
              /*implyR(1) &*/ printIndexed("step w=-1 | w=1") &
              by(invariantWe)
              ,

            /*usecase*/ sublabel("W(w) loop use") & /*implyR(1) &*/ closeId
          )
            // end postCut(w)
            ,

          /*use*/ sublabel("A()&W(w) augmented") & DebuggingTactics.assert(And(w,e), "W&Ce")(-2) & andL(-2) & printIndexed("inductive use of A&W") &
            cutL(i)(-3) & Idioms.<(
            /*show*/ hide(1) & label("by seq-equiv") & equivifyR(1) & by(seqEquivalence),

            /*use*/ sublabel("Ce~>Ci reduction") & label("Ce~>Ci reduction") & printIndexed("Ce~>Ci reduction") &
              useAt(postEquivalence)(1, 1::Nil)//CE(postEquivalence)(1, 1::Nil)
              & printIndexed("Ce~>Ci reduced in postcondition")
              & printIndexed("unpack and repack to replace test") &
              /*loop(And(w,And(u, i)))(1)*/
              loop(And(a,And(w,And(u1, And(u2, i)))))(1)
              & sublabel("loop induction")
              & Idioms.<(
              /*init*/ sublabel("W&u&Ci init") & printIndexed("W&u&Ci init") &
                andR(1) & Idioms.<(closeId , andR(1) & Idioms.<(closeId, andR(1) & Idioms.<(
                label("arith") /*& done*/
                  & printIndexed("A&W(w)&Ci->u")
                  & printIndexed("Using ucLoLemma") &
                  assertE(ucLoLemma.conclusion.succ.head, "ucLoLemma not applicable, have unexpected goal")(1) & by(ucLoLemma)
                , andR(1) & Idioms.<(closeId, closeId)))),

              /*step*/ sublabel("W&u&Ci step") & // hide(And(w,And(u,i)))(-4) & hide(i)(-3) & hide(w)(-2) &
                andL(-1) & assertE(a, "A()")(-1) & printIndexed("W&u&Ci step") &
                boxAnd(1) & andR(1) & Idioms.<(
                // A() invariant
                V(1) & closeId
                ,
                // implyR(1) &
                boxAnd(1) & andR(1) & Idioms.<(
                  // W(w) invariant
                  printIndexed("W invariant again") &
                    andL(-2) & andL(-3) & andL(-4)
                    & hideL(-5, i) & hideL(-3, u1) & hideL(-1, a) & /* hide duplicate w*/ hideL(-1, w) &
                    by(invariantWe)
                  ,
                  // u&Ce invariant
                  composeb(1) & composeb(1) & choiceb(1)  // unpack
                    //& useAt("[;] compose", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil))  // gather
                    & composeb(1, 1::Nil) & composeb(1, 1::1::Nil) & composeb(1, 1::1::1::Nil) & composeb(1, 1::1::1::1::Nil)
                    & printIndexed("cutting explicit dynamics away")
                    & cutAt(i0)(1, 1::1::1::1::1::0::0::Nil) & printIndexed("cuttedAt") & Idioms.<(
                    /*show*/ sublabel("show patch") & printIndexed("showing patch")
                      & useAt("-> distributes over &", PosInExpr(0::Nil))(1)
                      & andR(1) & Idioms.<(
                      // left branch is unchanged
                      sublabel("cutAt no change on left") & implyR(1) & andL(-3) & closeId
                      ,
                      // right branch replaced implicit with explicit conditionally
                      sublabel("CMon++")
                        & printIndexed("CMon++")
                        & useAt("& commute")(1, 0::Nil)
                        & printIndexed("& commuted")
                        & useAt("-> weaken", PosInExpr(1::Nil))(1)
                        & printIndexed("-> weakened")
                        & label("CMon") & printIndexed("CMon")
                        & sublabel("-> weakened")
                        // the following is like CMon(PosInExpr(1::1::1::0::0::Nil)) except with context kept around
                        & implyR(1)
                        & printIndexed("->R ed")
                        // gather outer [dhf:=*;][w:=-1;++w:=1;] boxes to single [;]
                        & sublabel("gathering") & printIndexed("gathering")
                        // A(), W(w)&u&Ci((w,dhf)), [dhf:=*;][w:=-1;++w:=1;][?Ci((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))  ==>  [dhf:=*;][w:=-1;++w:=1;][?Ce((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))
                        & useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::Nil)
                        & useAt("[;] compose", PosInExpr(1::Nil))(1, 1::Nil)
                        & useAt("[;] compose", PosInExpr(1::Nil))(1)
                        & useAt("[;] compose", PosInExpr(1::Nil))(-3, 1::1::Nil)
                        & useAt("[;] compose", PosInExpr(1::Nil))(-3, 1::Nil)
                        & useAt("[;] compose", PosInExpr(1::Nil))(-3)
                        & printIndexed("gathered")
                        // A(), W(w)&u&Ci((w,dhf)), [dhf:=*;{w:=-1;++w:=1;}][?Ci((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))  ==>  [dhf:=*;{w:=-1;++w:=1;}][?Ce((w,dhf));][ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci((w,dhf)))
                        & sublabel("postCut A()&W(w0)") & printIndexed("postCut A()&W(w0)")
                        & postCut(And(a,w0))(1) & Idioms.<(
                        /*show*/ sublabel("generalize post A()&W(w0)") & printIndexed("generalize post A()&W(w0)")
                          & hide(-3) & printIndexed("Hide expects " + And(w0,And(u0,And(w0, i0))).prettyString)
                          & hideL(-2, And(w0,And(u0,And(w0, i0)))) & sublabel("chasing") & chase(1)
                          & allR(1) & allR(1) // equivalent:  HilbertCalculus.vacuousAll(1)
                          & sublabel("gen by arith") & printIndexed("gen by arith")
                          & andR(1) & Idioms.<(
                          andR(1) & Idioms.<(
                            closeId
                            ,
                            done // QE
                            )
                          ,
                          andR(1) & Idioms.<(
                            closeId
                            ,
                            done //QE
                            )
                          )
                          , // generalize post A()&W(w0)

                        /*use*/ sublabel("generalized A()&W(w0)->post")
                          & testb(1, 1::1::Nil)
                          & printIndexed("do use dist equiv impl")
                          & assertE(And(a,w0), "do use dist equiv form")(1, 1::0::Nil)
                          & assertE(e0, "do use dist equiv form")(1, 1::1::0::Nil)
                          & assertE("to:=0;dhf:=*;dhfM:=*;{w:=-1;++w:=1;}".asProgram, "do use dist equiv form")(1, 0::Nil)
                          & assertE("ao:=*;".asProgram, "do use dist equiv form")(1, 1::1::1::0::Nil)
                          // [dhf:=*;{w:=-1;++w:=1;}]__(A()&W(w)->Ce(w,dhf) -> [ao:=*;][{r'=-rv,dhd'=ao,h'=-dhd&w*dhd>=w*dhf|w*ao>=a}](u&Ci))__
                          //@todo why will this guy keep around an extra premise??
                          // __(A()&W(w_0) -> Ce(w_0,dhf_0) -> q())__  <->  (A()&W(w_0) -> Ci(w_0,dhf_0) -> q())
                          & useAt(distEquivImpl, PosInExpr(0::Nil))(1, 1::Nil)
                          & sublabel("dist equiv impl")
                          & printIndexed("used dist equiv impl")
                          & assertE(And(a,w0), "used dist equiv form")(1, 1::0::Nil)
                          & assertE(i0, "used dist equiv form")(1, 1::1::0::Nil)
                          & assertE("to:=0;dhf:=*;dhfM:=*;{w:=-1;++w:=1;}".asProgram, "used dist equiv form")(1, 0::Nil)
                          & assertE("ao:=*;".asProgram, "used dist equiv form")(1, 1::1::1::0::Nil)
                          //                      & (if (distEquivImpl.isProved) {
                          //                      assertE("dhf_0:=*;{w_0:=-1;++w_0:=1;}".asProgram, "used dist equiv form")(1, 0 :: Nil) &
                          //                        assertE ("ao:=*;".asProgram, "used dist equiv form")(1, 1::1::1::0::Nil)
                          //                    } else {
                          //                    //  println("WARN: unproved distEquivImpl, so proof goals will remain around");
                          //                      skip
                          //                    })
                          // repacking
                          & useAt("[?] test", PosInExpr(1::Nil))(1, 1::1::Nil)
                          & printIndexed("repacked test")
                          // drop a&w implication from postcondition again
                          //& useAt("K modal modus ponens", PosInExpr(0::Nil))(1) & implyR(1) & hide(-4)
                          & sublabel("[] post weaken")
                          & printIndexed("do [] post weaken")
                          & assertE(And(a,w0), "post weaken form")(1, 1::0::Nil)
                          & assertE(Test(i0), "post weaken form")(1, 1::1::0::Nil)
                          & useAt("[] post weaken", PosInExpr(1::Nil))(1) //& useAt("[] post weaken")(1, /*Nil*/1::1::1::Nil)
                          & printIndexed("did [] post weaken")
                          & close(-3, 1)
                          // successfully closes
                          // generalized A()&W(w0)->post
                      )  // postCut(And(a,w0))
                      )  // andR within show patch
                      // show patch
                    ,

                    /*use*/ sublabel("use patch") & printIndexed("use patch")
                      // repacking
                      & useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::1::1::Nil)
                      & useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::1::Nil)
                      & useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::Nil)
                      & useAt("[;] compose", PosInExpr(1::Nil))(1, 1::Nil)
                      //& useAt("[;] compose", PosInExpr(0::Nil))(SuccPosition(0, 1::Nil))// ungather
                      // repack
                      & useAt("[++] choice", PosInExpr(1::Nil))(1)
                      & useAt("[;] compose", PosInExpr(1::Nil))(1)
                      & useAt("[;] compose", PosInExpr(1::Nil))(1)
                      & label("use patch") & printIndexed("used patch")
                      // by unrolling implicit once
                      //@todo rename acasximplicit to w_0 names or vice versa ....
                      & cut(acasximplicit.asInstanceOf[Imply].right) & Idioms.<(
                      /*show*/ sublabel("show implicit applicable") &
                          hide(1) &
                          cut(acasximplicit) & Idioms.<(
                          /*show*/ cohide(2) & sublabel("lookup lemma") & label("") & by(acasximplicitP),
                          /*use*/ sublabel("show lemma assumptions") & label("") & printIndexed("show lemma assumptions") &
                              implyL(-3) & Idioms.<(
                              hide(1) &
                                label("step 1") &
                                // prove A()&(W(w)&Ci(w,dhf))
                                andR(1) & Idioms.<(
                                label("A id") & close(-1,1)
                                ,
                                // split W(w)&u&Ci finally
                                label("step W(w)&Ci") & printIndexed("step W(w)&Ci") &
                                  andL(-2) & andL(-3) & andL(-4) &
                                  andR(1) & Idioms.<(
                                  label("W(w) id") & closeId // (-2,1)
                                  ,
                                  label("Ci id") & closeId //(-4,1)
                                  /*andR(1) & (
                                    label("arithmetic")
                                    ,
                                    label("Ci id") & closeId //(-4,1)
                                    )
                                    */
                                  )
                                )
                              ,
                              label("looked up") & closeId)
                        )
                        ,  // show implicit applicable

                      /*use*/ sublabel("by implicit") & useAt("[*] approx")(-3) & closeId
                    )
                    // use patch
                  )  // cutAt(i0)
                  )  // u&Ce invariant
                )
                ,  // W(w)&Ci step

              /*usecase*/ sublabel("final use") & printIndexed("final use") & andL(-1) & andL(-2) & andL(-3)
                & implyR(1) & implyR(1)
                & andR(1) & onAll(closeId)
            ) // ind(And(a,And(w,And(u, i))))
          ) // cutL(i)(-3)
        )
      ) // postCut(a)
    )

    proof
  }

}
