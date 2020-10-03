package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.SaturateTactic
import edu.cmu.cs.ls.keymaerax.btactics.ODEStability._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ElidingProvable


class ODEStabilityTests extends TacticTestBase {

  "stability" should "prove stability for pendulum" in withMathematica { _ =>
    val ode = "theta' = w, w'= -a*theta - b*w".asDifferentialProgram
    val stable = stabODE(ode)
    val attractive = attrODE(ode)

    // Lyapunov function a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4
    // The conditions of Lyapunov's theorem is satisfied globally, which gives an easier proof (choosing \tau = \eps)
    val qe = proveBy("a>0&b>0, eps>0 ==> \\exists bnd (bnd>0&\\forall theta \\forall w ((theta*theta+w*w < 1*1)&!theta*theta+w*w < eps*eps->-(a*(2*theta*w)*2/4+(2*(b*theta+w)*(b*w+(-a*theta-b*w))+2*w*(-a*theta-b*w))*4/16)>=bnd))".asSequent,
      QE)

    val pr1 = proveBy(Imply("a > 0 & b > 0".asFormula,stable),
      unfoldProgramNormalize &
        //On ||x||=eps, there is a global lower bound on k
        cutR("\\exists k (k > 0 & \\forall theta \\forall w (theta*theta+w*w = eps*eps -> a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 >= k))".asFormula)(1) <(
          QE,
          unfoldProgramNormalize &
            //There is del s.t. ||x||<del -> v < k
            cutR("\\exists del (del > 0 & del < eps & \\forall theta \\forall w (theta*theta+w*w < del*del -> a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 < k))".asFormula)(1) <(
              hideL('Llast) & QE,
              unfoldProgramNormalize &
                existsR("del".asTerm)(1) & andR(1) <(
                prop,
                unfoldProgramNormalize &
                  allL(-8) & allL(-8) & //theta, w
                  implyL(-8) <(
                    hideR(1) & prop,
                    // Move the forall quantified antecedent into domain constraint
                    // TODO: make tactic that adds universals directly into domain (without the universals)
                    dC("theta*theta+w*w=eps*eps->a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4>=k".asFormula)(1) <(
                      hideL(-5) &
                        // This part is slightly simpler without having to close over the sub-domain
                        dC("a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 < k".asFormula)(1) <(
                          ODE(1),
                          ODE(1)
                        )
                      ,
                      dWPlus(1) & allL(-5) & allL(-5) & prop
                    )
                  )
              )
            )
        )
    )

    // The important direction of SAttr
    val pr2 = proveBy(
      Imply(And(stable,"\\forall eps (eps>0-><{theta'=w,w'=-a*theta-b*w&true}>theta*theta+w*w < eps*eps)".asFormula),
        "\\forall eps (eps>0-><{theta'=w,w'=-a*theta-b*w&true}>[{theta'=w,w'=-a*theta-b*w&true}]theta*theta+w*w < eps*eps)".asFormula),
      implyR(1) & andL(-1) & allR(1) & implyR(1) &
      allL(-1) & implyL(-1) <(
        prop,
        existsL(-1) & allL("del".asTerm)(-1) &
        implyL(-1) <(
          prop,
          ODELiveness.kDomainDiamond("theta*theta+w*w < del*del".asFormula)(1) <(
            prop,
            andL('Llast) &
            // Move the forall quantified antecedent into domain constraint
            // TODO: make tactic that adds universals directly into domain (without the universals)
            dC("(theta*theta+w*w < del*del->[{theta'=w,w'=-a*theta-b*w&true}]theta*theta+w*w < eps*eps)".asFormula)(1) <(
              dW(1) & prop,
              dWPlus(1) & allL(-3) & allL(-3) & close
            )
          )
        )
      )
    )

    // The important direction of SAttr + some quantifiers
    val pr3 = proveBy(
    Imply(And(stable,"\\exists del (del>0&\\forall theta \\forall w (theta*theta+w*w < del*del->\\forall eps (eps>0-><{theta'=w,w'=-a*theta-b*w&true}>theta*theta+w*w < eps*eps)))".asFormula),
      attractive),
      implyR(1) & andL(-1) & existsL(-2) & andL(-2) & existsR(1) & andR(1) <(
        prop,
        allR(1) & allR(1) & implyR(1) &
        //weird
        cutR(And(stable,"\\forall eps (eps>0-><{theta'=w,w'=-a*theta-b*w&true}>theta*theta+w*w < eps*eps)".asFormula))(1) <(
          andR(1) <(prop, allL(-3) & allL(-3) & implyL(-3) <(prop,prop) ),
          cohideR(1) & byUS(pr2)
        )
      )
    )

    val pr4 = proveBy( Imply("a > 0 & b > 0".asFormula, Imply(stable, attractive)),
      implyR(1) &
        implyR(1) &
      cutR(And(stable,"\\exists del (del>0&\\forall theta \\forall w (theta*theta+w*w < del*del->\\forall eps (eps>0-><{theta'=w,w'=-a*theta-b*w&true}>theta*theta+w*w < eps*eps)))".asFormula))(1)<(
        andR(1) <( prop,
          allL(Number(1))(-2) & // Because of global-ness, we can pick any arbitrary epsilon here
          implyL(-2) <(
            cohideR(2) & QE,
            existsL(-2) & existsR(1) & andR(1) <(
              prop,
              allR(1) & allR(1) &
              andL(-2) & implyR(1) & allL(-3) & allL(-3) & implyL(-3) <(
                prop,
                allR(1) & implyR(1) &
                ODELiveness.saveBox(1) &
                cutR("\\exists bnd \\forall theta \\forall w (theta*theta+w*w < 1 * 1 -> a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 >= bnd)".asFormula)(1) <(
                  cohideR(1) & QE,
                  implyR(1) & existsL('Llast) &
                  ODELiveness.kDomainDiamond("a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 < bnd ".asFormula)(1) <(
                    hideL(-7) & hideL(-4) & hideL(-2) & ODELiveness.dV(None)(1) &
                      //Nasty
                      cutR("\\exists bnd (bnd>0&\\forall theta \\forall w ((theta*theta+w*w < 1*1)&!theta*theta+w*w < eps*eps->-(a*(2*theta*w)*2/4+(2*(b*theta+w)*(b*w+(-a*theta-b*w))+2*w*(-a*theta-b*w))*4/16)>=bnd))".asFormula)(1) <(
                        byUS(qe),
                        implyR(1) & existsL(-3) & existsR("bnd".asTerm)(1) & andR(1) <(
                          prop,
                          andL('Llast) & cohideOnlyL('Llast) & unfoldProgramNormalize &
                          allL(-1) & allL(-1) & implyL(-1) <(prop, prop)
                        )
                      ),
                    dWPlus(1) & allL(-5) & allL(-5) & QE //can be done propositionally
                  )
                )
              )
            )
          )
        ),
        cohideR(1) & byUS(pr3))
    )

    // Propositional manipulation
    val pr5 = proveBy( Imply("a > 0 & b > 0".asFormula, And(stable , attractive)),
      implyR(1) & cutR( And(stable , Imply(stable,attractive)) )(1) <(
        andR(1) <(
          implyRi & byUS(pr1),
          implyRi & byUS(pr4)
        ),
        prop
      )
    )

    println(pr5)
    pr5 shouldBe 'proved
  }

  it should "prove 3rd order stability for pendulum" in withMathematica { _ =>
    val ode = "theta' = w, w'= -a*(theta - theta^3/6) - b*w".asDifferentialProgram
    val stable = stabODE(ode)
    val attractive = attrODE(ode)

    val lyap = "a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4".asTerm
    val lie = DifferentialHelper.simplifiedLieDerivative(ode,lyap, ToolProvider.simplifierTool())
    println(lie)

//    val pr1 = proveBy(Imply("a > 0 & b > 0".asFormula,stable),
//      unfoldProgramNormalize &
//      cutR("\\exists tau (tau > 0 & tau < eps & \\forall theta \\forall w (theta*theta+w*w <= tau*tau -> 1/12*((-6)*b*w^2+a*theta^2*(b*((-6)+theta^2)+2*theta*w)) <= 0))".asFormula)(1) <(
//        QE,
//        unfoldProgramNormalize &
//        //On ||x||=tau, there is a global lower bound on k
//        cutR("\\exists k (k > 0 & \\forall theta \\forall w (theta*theta+w*w = tau*tau -> a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 >= k))".asFormula)(1) <(
//          hideL('Llast) & QE,
//          unfoldProgramNormalize &
//          //There is del s.t. ||x||<del -> v < k
//          cutR("\\exists del (del > 0 & del < tau & \\forall theta \\forall w (theta*theta+w*w < del*del -> a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 < k))".asFormula)(1) <(
//            hideL('Llast) & hideL(-6) & QE,
//            unfoldProgramNormalize &
//            existsR("del".asTerm)(1) & andR(1) <(
//              prop,
//              unfoldProgramNormalize &
//              allL(-11) & allL(-11) & //theta, w
//              implyL(-11) <(
//                hideR(1) & prop,
//                generalize("theta*theta+w*w < tau*tau".asFormula)(1) <(
//                  hideL(-5) & hideL(-3) &
//                  ODEInvariance.dCClosure(1) <(
//                    hideL(-6) & hideL(-4) & QE,
//                    dC("theta*theta+w*w=tau*tau->a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4>=k".asFormula)(1) <(
//                      hideL(-6) &
//                      dC("1/12*((-6)*b*w^2+a*theta^2*(b*((-6)+theta^2)+2*theta*w))<=0".asFormula)(1) <(
//                        hideL(-4) &
//                          dC("a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 < k".asFormula)(1) <(
//                            ODE(1),
//                            ODE(1)
//                          ),
//                        dWPlus(1) & allL(-4) & allL(-4) & QE
//                      )
//                      ,
//                      dWPlus(1) & allL(-6) & allL(-6) & prop
//                    )
//                  ),
//                  QE
//                )
//              )
//            )
//          )
//        )
//      )
//    )

    // The important direction of SAttr
    val pr2 = proveBy(
      Imply(And(stable,"\\forall eps (eps>0-><{theta'=w,w'= -a*(theta - theta^3/6)-b*w&true}>theta*theta+w*w < eps*eps)".asFormula),
        "\\forall eps (eps>0-><{theta'=w,w'= -a*(theta - theta^3/6)-b*w&true}>[{theta'=w,w'= -a*(theta - theta^3/6)-b*w&true}]theta*theta+w*w < eps*eps)".asFormula),
      implyR(1) & andL(-1) & allR(1) & implyR(1) &
        allL(-1) & implyL(-1) <(
        prop,
        existsL(-1) & allL("del".asTerm)(-1) &
          implyL(-1) <(
            prop,
            ODELiveness.kDomainDiamond("theta*theta+w*w < del*del".asFormula)(1) <(
              prop,
              andL('Llast) &
                // Move the forall quantified antecedent into domain constraint
                // TODO: make tactic that adds universals directly into domain (without the universals)
                dC("(theta*theta+w*w < del*del->[{theta'=w,w'= -a*(theta - theta^3/6)-b*w&true}]theta*theta+w*w < eps*eps)".asFormula)(1) <(
                  dW(1) & prop,
                  dWPlus(1) & allL(-3) & allL(-3) & close
                )
            )
          )
      )
    )

    // The important direction of SAttr + some quantifiers
    val pr3 = proveBy(
      Imply(And(stable,"\\exists del (del>0&\\forall theta \\forall w (theta*theta+w*w < del*del->\\forall eps (eps>0-><{theta'=w,w'= -a*(theta - theta^3/6)-b*w&true}>theta*theta+w*w < eps*eps)))".asFormula),
        attractive),
      implyR(1) & andL(-1) & existsL(-2) & andL(-2) & existsR(1) & andR(1) <(
        prop,
        allR(1) & allR(1) & implyR(1) &
          //weird
          cutR(And(stable,"\\forall eps (eps>0-><{theta'=w,w'= -a*(theta - theta^3/6)-b*w&true}>theta*theta+w*w < eps*eps)".asFormula))(1) <(
            andR(1) <(prop, allL(-3) & allL(-3) & implyL(-3) <(prop,prop) ),
            cohideR(1) & byUS(pr2)
          )
      )
    )
//    val qe = proveBy(("\\forall theta \\forall w ((theta*theta+w*w <= 1*1)&!theta*theta+w*w < eps*eps->-(a*(2*theta*w)*2/4+(2*(b*theta+w)*(b*w+(-a*(theta-theta^3/6)-b*w))+2*w*(-a*(theta-theta^3/6)-b*w))*4/16)>0) ==>" +
//      "\\exists bnd (bnd>0&\\forall theta \\forall w ((theta*theta+w*w <= 1*1)&!theta*theta+w*w < eps*eps->-(a*(2*theta*w)*2/4+(2*(b*theta+w)*(b*w+(-a*(theta-theta^3/6)-b*w))+2*w*(-a*(theta-theta^3/6)-b*w))*4/16)>=bnd))").asSequent,
//      QE)
//    println(qe)
//
//    val pr4 = proveBy( Imply("a > 0 & b > 0".asFormula, Imply(stable, attractive)),
//      implyR(1) &
//        implyR(1) &
//        cutR(And(stable,"\\exists del (del>0&\\forall theta \\forall w (theta*theta+w*w < del*del->\\forall eps (eps>0-><{theta'=w,w'=-a*(theta - theta^3/6)-b*w&true}>theta*theta+w*w < eps*eps)))".asFormula))(1)<(
//          andR(1) <( prop,
//          //This QE is pretty repeated
//          cutR("\\exists tau (tau > 0 & \\forall theta \\forall w (0 < theta*theta+w*w & theta*theta+w*w <= tau*tau -> 1/12*((-6)*b*w^2+a*theta^2*(b*((-6)+theta^2)+2*theta*w)) < 0))".asFormula)(1) <(
//            hideL(-2) & QE,
//            implyR(1) & existsL('Llast) & andL('Llast) &
//            allL("tau".asTerm)(-2) &
//              implyL(-2) <(
//                prop,
//                existsL(-2) & existsR(1) & andR(1) <(
//                  prop,
//                  allR(1) & allR(1) &
//                  andL(-4) & implyR(1) & allL(-5) & allL(-5) & implyL(-5) <(
//                    prop,
//                    allR(1) & implyR(1) &
//                    ODELiveness.saveBox(1) &
//                    cutR("\\exists bnd \\forall theta \\forall w (theta*theta+w*w < tau * tau -> a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 >= bnd)".asFormula)(1) <(
//                      cohideR(1) & QE,
//                      implyR(1) & existsL('Llast) &
//                        DebuggingTactics.print("foo") &
//                        ODELiveness.kDomainDiamond("a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 < bnd ".asFormula)(1) <(
//                          hideL(-7) & ODELiveness.dV(None)(1) & skip,
////                            //Nasty
////                            cutR("\\exists bnd (bnd>0&\\forall theta \\forall w ((theta*theta+w*w < 1*1)&!theta*theta+w*w < eps*eps->-(a*(2*theta*w)*2/4+(2*(b*theta+w)*(b*w+(-a*theta-b*w))+2*w*(-a*theta-b*w))*4/16)>=bnd))".asFormula)(1) <(
////                              byUS(qe),
////                              implyR(1) & existsL(-3) & existsR("bnd".asTerm)(1) & andR(1) <(
////                                prop,
////                                andL('Llast) & cohideOnlyL('Llast) & unfoldProgramNormalize &
////                                  allL(-1) & allL(-1) & implyL(-1) <(prop, prop)
//                          dWPlus(1) & allL(-7) & allL(-7) & hideL(-3) & QE //can be done propositionally
//                        )
//                    )
//                  )
//                )
//              )
//            )
//          ),
//          cohideR(1) & byUS(pr3))
//    )
////
////    // Propositional manipulation
////    val pr5 = proveBy( Imply("a > 0 & b > 0".asFormula, And(stable , attractive)),
////      implyR(1) & cutR( And(stable , Imply(stable,attractive)) )(1) <(
////        andR(1) <(
////          implyRi & byUS(pr1),
////          implyRi & byUS(pr4)
////        ),
////        prop
////      )
////    )
//
//    println(pr4)
//    pr5 shouldBe 'proved
  }
}
