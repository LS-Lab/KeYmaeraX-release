package btactics

import edu.cmu.cs.ls.keymaerax.btactics.ODEStability._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest

@SlowTest
class ODEStabilityTests extends TacticTestBase {

  "stability" should "prove stability for pendulum" in withMathematica { _ =>
    val ode = "theta' = w, w'= -a()*theta - b()*w".asDifferentialProgram
    val stable = stabODE(ode)
    val attractive = attrODE(ode)

    // Lyapunov function a()*(theta^2)/2 + ((b()*theta+w)^2+w^2)/4
    // The conditions of Lyapunov's theorem is satisfied globally, which gives an easier proof (choosing \tau = \eps)
    val qe = proveBy("a()>0&b()>0, eps>0 ==> \\exists bnd (bnd>0&\\forall theta \\forall w ((theta*theta+w*w < 1*1)&!theta*theta+w*w < eps*eps->-(a()*(2*theta*w)*2/4+(2*(b()*theta+w)*(b()*w+(-a()*theta-b()*w))+2*w*(-a()*theta-b()*w))*4/16)>=bnd))".asSequent,
      QE)

    val pr1 = proveBy(Imply("a() > 0 & b() > 0".asFormula,stable),
      unfoldProgramNormalize &
        //On ||x||=eps, there is a global lower bound on k
        cutR("\\exists k (k > 0 & \\forall theta \\forall w (theta*theta+w*w = eps*eps -> a()*(theta^2)/2 + ((b()*theta+w)^2+w^2)/4 >= k))".asFormula)(1) <(
          QE,
          unfoldProgramNormalize &
            //There is del s.t. ||x||<del -> v < k
            cutR("\\exists del (del > 0 & del < eps & \\forall theta \\forall w (theta*theta+w*w < del*del -> a()*(theta^2)/2 + ((b()*theta+w)^2+w^2)/4 < k))".asFormula)(1) <(
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
                    dC("theta*theta+w*w=eps*eps->a()*(theta^2)/2 + ((b()*theta+w)^2+w^2)/4>=k".asFormula)(1) <(
                      hideL(-5) &
                        // This part is slightly simpler without having to close over the sub-domain
                        dC("a()*(theta^2)/2 + ((b()*theta+w)^2+w^2)/4 < k".asFormula)(1) <(
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
      Imply(And(stable,"\\forall eps (eps>0-><{theta'=w,w'=-a()*theta-b()*w&true}>theta*theta+w*w < eps*eps)".asFormula),
        "\\forall eps (eps>0-><{theta'=w,w'=-a()*theta-b()*w&true}>[{theta'=w,w'=-a()*theta-b()*w&true}]theta*theta+w*w < eps*eps)".asFormula),
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
            dC("(theta*theta+w*w < del*del->[{theta'=w,w'=-a()*theta-b()*w&true}]theta*theta+w*w < eps*eps)".asFormula)(1) <(
              dW(1) & prop,
              dWPlus(1) & allL(-3) & allL(-3) & close
            )
          )
        )
      )
    )

    // The important direction of SAttr + some quantifiers
    val pr3 = proveBy(
    Imply(And(stable,"\\exists del (del>0&\\forall theta \\forall w (theta*theta+w*w < del*del->\\forall eps (eps>0-><{theta'=w,w'=-a()*theta-b()*w&true}>theta*theta+w*w < eps*eps)))".asFormula),
      attractive),
      implyR(1) & andL(-1) & existsL(-2) & andL(-2) & existsR(1) & andR(1) <(
        prop,
        allR(1) & allR(1) & implyR(1) &
        //weird
        cutR(And(stable,"\\forall eps (eps>0-><{theta'=w,w'=-a()*theta-b()*w&true}>theta*theta+w*w < eps*eps)".asFormula))(1) <(
          andR(1) <(prop, allL(-3) & allL(-3) & implyL(-3) <(prop,prop) ),
          cohideR(1) & byUS(pr2)
        )
      )
    )

    val pr4 = proveBy( Imply("a() > 0 & b() > 0".asFormula, Imply(stable, attractive)),
      implyR(1) &
        implyR(1) &
      cutR(And(stable,"\\exists del (del>0&\\forall theta \\forall w (theta*theta+w*w < del*del->\\forall eps (eps>0-><{theta'=w,w'=-a()*theta-b()*w&true}>theta*theta+w*w < eps*eps)))".asFormula))(1)<(
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
                cutR("\\exists bnd \\forall theta \\forall w (theta*theta+w*w < 1 * 1 -> a()*(theta^2)/2 + ((b()*theta+w)^2+w^2)/4 >= bnd)".asFormula)(1) <(
                  cohideR(1) & QE,
                  implyR(1) & existsL('Llast) &
                  ODELiveness.kDomainDiamond("a()*(theta^2)/2 + ((b()*theta+w)^2+w^2)/4 < bnd ".asFormula)(1) <(
                    hideL(-7) & hideL(-4) & hideL(-2) & ODELiveness.dV(None)(1) &
                      //Nasty
                      cutR("\\exists bnd (bnd>0&\\forall theta \\forall w ((theta*theta+w*w < 1*1)&!theta*theta+w*w < eps*eps->-(a()*(2*theta*w)*2/4+(2*(b()*theta+w)*(b()*w+(-a()*theta-b()*w))+2*w*(-a()*theta-b()*w))*4/16)>=bnd))".asFormula)(1) <(
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
    val pr5 = proveBy( Imply("a() > 0 & b() > 0".asFormula, And(stable , attractive)),
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

  it should "prove global exponential stability for pendulum" in withMathematica { _ =>
    val ode = "theta' = w, w'= -a()*theta - b()*w".asDifferentialProgram
    val estable = estabODEP(ode,True)

    val pr1 = proveBy(Imply("a() = 1 & b() =1".asFormula,estable),
      implyR(1) & andL(-1) & exhaustiveEqL2R(-1) &  exhaustiveEqL2R(-2) &
      existsR("2".asTerm)(1)<(
        andR(1) <(
          QE,
          existsR("1/4".asTerm)(1) & andR(1) <(
            QE,
            unfoldProgramNormalize &
            dC("(theta^2)/2 + ((theta+w)^2+w^2)/4 <= 1/4 * aux".asFormula)(1) <(
              ODE(1),
              ODE(1)
            )
          )
        )
      )
    )

    println(pr1)
    pr1 shouldBe 'proved
  }

  it should "prove stability for inverted pendulum" taggedAs testHelper.KeYmaeraXTestTags.SlowTest in withMathematica { _ =>
    val ode = "theta' = w, w'= a()*theta - b()*w - (k1() * theta + k2() * w)".asDifferentialProgram
    val stable = stabODE(ode)
    val attractive = attrODE(ode)

    // Lyapunov function (k1()-a())*(theta^2)/2 + (((b()+k2())*theta+w)^2+w^2)/4
    val qe = proveBy("a()>0&b()>=0&k1()>a()&k2()>-b(), eps>0 ==> \\exists bnd (bnd>0&\\forall theta \\forall w ((theta*theta+w*w < 1*1)&!theta*theta+w*w < eps*eps->-((k1()-a())*(2*theta*w)*2/4+(2*((b()+k2())*theta+w)*((b()+k2())*w+(a()*theta-b()*w-(k1()*theta+k2()*w)))+2*w*(a()*theta-b()*w-(k1()*theta+k2()*w)))*4/16)>=bnd))".asSequent,
      QE)

    val pr1 = proveBy(Imply("a() > 0 & b() >= 0 & k1() > a() & k2() > -b()".asFormula,stable),
      unfoldProgramNormalize &
        //On ||x||=eps, there is a global lower bound on k
        cutR("\\exists k (k > 0 & \\forall theta \\forall w (theta*theta+w*w = eps*eps -> (k1()-a())*(theta^2)/2 + (((b()+k2())*theta+w)^2+w^2)/4 >= k))".asFormula)(1) <(
          QE,
          unfoldProgramNormalize &
            //There is del s.t. ||x||<del -> v < k
            cutR("\\exists del (del > 0 & del < eps & \\forall theta \\forall w (theta*theta+w*w < del*del -> (k1()-a())*(theta^2)/2 + (((b()+k2())*theta+w)^2+w^2)/4 < k))".asFormula)(1) <(
              hideL('Llast) & QE,
              unfoldProgramNormalize &
                existsR("del".asTerm)(1) & andR(1) <(
                prop,
                unfoldProgramNormalize &
                  allL(-10) & allL(-10) & //theta, w
                  implyL(-10) <(
                    hideR(1) & prop,
                    // Move the forall quantified antecedent into domain constraint
                    // TODO: make tactic that adds universals directly into domain (without the universals)
                    dC("theta*theta+w*w=eps*eps->(k1()-a())*(theta^2)/2 + (((b()+k2())*theta+w)^2+w^2)/4>=k".asFormula)(1) <(
                      hideL(-5) &
                        // This part is slightly simpler without having to close over the sub-domain
                        dC("(k1()-a())*(theta^2)/2 + (((b()+k2())*theta+w)^2+w^2)/4 < k".asFormula)(1) <(
                          ODEInvariance.sAIRankOne()(1),
                          dR(True)(1)< ( dI('full)(1), ODE(1))
                        )
                      ,
                      dWPlus(1) & allL(-7) & allL(-7) & prop
                    )
                  )
              )
            )
        )
    )

    // The important direction of SAttr
    val pr2 = proveBy(
      Imply(And(stable,"\\forall eps (eps>0-><{theta'=w,w'=a()*theta - b()*w - (k1() * theta + k2() * w)&true}>theta*theta+w*w < eps*eps)".asFormula),
        "\\forall eps (eps>0-><{theta'=w,w'=a()*theta - b()*w - (k1() * theta + k2() * w)&true}>[{theta'=w,w'=a()*theta - b()*w - (k1() * theta + k2() * w)&true}]theta*theta+w*w < eps*eps)".asFormula),
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
                dC("(theta*theta+w*w < del*del->[{theta'=w,w'=a()*theta - b()*w - (k1() * theta + k2() * w)&true}]theta*theta+w*w < eps*eps)".asFormula)(1) <(
                  dW(1) & prop,
                  dWPlus(1) & allL(-3) & allL(-3) & close
                )
            )
          )
      )
    )

    // The important direction of SAttr + some quantifiers
    val pr3 = proveBy(
      Imply(And(stable,"\\exists del (del>0&\\forall theta \\forall w (theta*theta+w*w < del*del->\\forall eps (eps>0-><{theta'=w,w'=a()*theta - b()*w - (k1() * theta + k2() * w)&true}>theta*theta+w*w < eps*eps)))".asFormula),
        attractive),
      implyR(1) & andL(-1) & existsL(-2) & andL(-2) & existsR(1) & andR(1) <(
        prop,
        allR(1) & allR(1) & implyR(1) &
          //weird
          cutR(And(stable,"\\forall eps (eps>0-><{theta'=w,w'=a()*theta - b()*w - (k1() * theta + k2() * w)&true}>theta*theta+w*w < eps*eps)".asFormula))(1) <(
            andR(1) <(prop, allL(-3) & allL(-3) & implyL(-3) <(prop,prop) ),
            cohideR(1) & byUS(pr2)
          )
      )
    )

    val pr4 = proveBy( Imply("a() > 0 & b() >= 0 & k1() > a() & k2() > -b()".asFormula, Imply(stable, attractive)),
      implyR(1) &
        implyR(1) &
        cutR(And(stable,"\\exists del (del>0&\\forall theta \\forall w (theta*theta+w*w < del*del->\\forall eps (eps>0-><{theta'=w,w'=a()*theta - b()*w - (k1() * theta + k2() * w)&true}>theta*theta+w*w < eps*eps)))".asFormula))(1)<(
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
                      cutR("\\exists bnd \\forall theta \\forall w (theta*theta+w*w < 1 * 1 -> (k1()-a())*(theta^2)/2 + (((b()+k2())*theta+w)^2+w^2)/4 >= bnd)".asFormula)(1) <(
                        cohideR(1) & QE,
                        implyR(1) & existsL('Llast) &
                          ODELiveness.kDomainDiamond("(k1()-a())*(theta^2)/2 + (((b()+k2())*theta+w)^2+w^2)/4 < bnd ".asFormula)(1) <(
                            hideL(-7) & hideL(-4) & hideL(-2) & ODELiveness.dV(None)(1) &
                              //Nasty
                              cutR("\\exists bnd (bnd>0&\\forall theta \\forall w ((theta*theta+w*w < 1*1)&!theta*theta+w*w < eps*eps->-((k1()-a())*(2*theta*w)*2/4+(2*((b()+k2())*theta+w)*((b()+k2())*w+(a()*theta-b()*w-(k1()*theta+k2()*w)))+2*w*(a()*theta-b()*w-(k1()*theta+k2()*w)))*4/16)>=bnd))".asFormula)(1) <(
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
    val pr5 = proveBy( Imply("a() > 0 & b() >= 0 & k1() > a() & k2() > -b()".asFormula, And(stable , attractive)),
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

  it should "prove stability for 1st and 3rd axis of rigid body" in withMathematica { _ =>
    val ode = "x1'=(I2()-I3())/I1() *x2*x3, x2'=(I3()-I1())/I2() *x3*x1, x3'=(I1()-I2())/I3()*x1*x2".asDifferentialProgram

    //Stability in x1 axis
    val stable1 = "\\forall eps (eps>0->\\exists del (del>0&\\forall x1 \\forall x2 \\forall x3 (x2*x2+x3*x3 < del*del->[{x1'=(I2()-I3())/I1()*x2*x3,x2'=(I3()-I1())/I2()*x3*x1,x3'=(I1()-I2())/I3()*x1*x2&true}]x2*x2+x3*x3 < eps*eps)))".asFormula
    //Stability in x3 axis
    val stable3 = "\\forall eps (eps>0->\\exists del (del>0&\\forall x1 \\forall x2 \\forall x3 (x1*x1+x2*x2 < del*del->[{x1'=(I2()-I3())/I1()*x2*x3,x2'=(I3()-I1())/I2()*x3*x1,x3'=(I1()-I2())/I3()*x1*x2&true}]x1*x1+x2*x2 < eps*eps)))".asFormula

    // Lyapunov function 1/2*((I1()-I2())/I3() *x2^2 - (I3()-I1())/I2()*x3^2)
    // Picking tau = eps
    val pr1 = proveBy(Imply("I1() > I2() & I2() > I3() & I3() > 0".asFormula,stable1),
      unfoldProgramNormalize &
        cutR(("\\exists k (" +
          "\\exists del (del > 0 & del < eps & \\forall x2 \\forall x3 (x2*x2+x3*x3 < del*del -> 1/2*((I1()-I2())/I3() *x2^2 - (I3()-I1())/I2()*x3^2)  < k)) &" +
          "\\forall x2 \\forall x3 (x2*x2+x3*x3 = eps*eps -> 1/2*((I1()-I2())/I3() *x2^2 - (I3()-I1())/I2()*x3^2) >= k))").asFormula)(1) <(
          QE,
          unfoldProgramNormalize &
          existsR("del".asTerm)(1) & andR(1) <(
          prop,
          unfoldProgramNormalize &
            allL(-8) & allL(-8) & implyL(-8) <(
              hideR(1) & prop,
              // Move the forall quantified antecedent into domain constraint
              // TODO: make tactic that adds universals directly into domain (without the universals)
              dC("x2*x2+x3*x3 = eps*eps -> 1/2*((I1()-I2())/I3() *x2^2 - (I3()-I1())/I2()*x3^2) >= k".asFormula)(1) <(
                hideL(-5) &
                  // This part is slightly simpler without having to close over the sub-domain
                  dC("1/2*((I1()-I2())/I3() *x2^2 - (I3()-I1())/I2()*x3^2)  < k".asFormula)(1) <(
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

    // Lyapunov function 1/2*(-(I3()-I1())/I2()*x1^2 + (I2()-I3())/I1() *x2^2)
    // Picking tau = eps
    val pr3 = proveBy(Imply("I1() > I2() & I2() > I3() & I3() > 0".asFormula,stable3),
      unfoldProgramNormalize &
        cutR(("\\exists k (" +
          "\\exists del (del > 0 & del < eps & \\forall x1 \\forall x2 (x1*x1+x2*x2 < del*del -> 1/2*(-(I3()-I1())/I2()*x1^2 + (I2()-I3())/I1() *x2^2)  < k)) &" +
          "\\forall x1 \\forall x2 (x1*x1+x2*x2 = eps*eps -> 1/2*(-(I3()-I1())/I2()*x1^2 + (I2()-I3())/I1() *x2^2) >= k))").asFormula)(1) <(
          QE,
          unfoldProgramNormalize &
            existsR("del".asTerm)(1) & andR(1) <(
            prop,
            unfoldProgramNormalize &
              allL(-8) & allL(-8) & implyL(-8) <(
              hideR(1) & prop,
              // Move the forall quantified antecedent into domain constraint
              // TODO: make tactic that adds universals directly into domain (without the universals)
              dC("x1*x1+x2*x2 = eps*eps -> 1/2*(-(I3()-I1())/I2()*x1^2 + (I2()-I3())/I1() *x2^2) >= k".asFormula)(1) <(
                hideL(-5) &
                  // This part is slightly simpler without having to close over the sub-domain
                  dC("1/2*(-(I3()-I1())/I2()*x1^2 + (I2()-I3())/I1() *x2^2)  < k".asFormula)(1) <(
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

    pr1 shouldBe 'proved
    pr3 shouldBe 'proved
  }

  it should "prove global asymptotic stability for 1st and 3rd axis of rigid body with friction" in withMathematica { _ =>
    val ode = "x1'=(I2()-I3())/I1() *x2*x3 - a1()*x1, x2'=(I3()-I1())/I2() *x3*x1 - a2()*x2, x3'=(I1()-I2())/I3()*x1*x2 - a3()*x3".asDifferentialProgram

    //Main parameter assumptions
    val Gamma = "I1() > I2() & I2() > I3() & I3() > 0 & a1() > 0 & a2() > 0 & a3() > 0".asFormula
    val stable1 = "\\forall eps (eps>0->\\exists del (del>0&\\forall x1 \\forall x2 \\forall x3 (x2*x2+x3*x3 < del*del->[{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}]x2*x2+x3*x3 < eps*eps)))".asFormula
    //Globally attractive
    val gattractive1 = "\\forall eps (eps>0-><{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}>[{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}]x2*x2+x3*x3 < eps*eps)".asFormula
    //Globally attractive (with stability)
    val gattractives1 = "\\forall eps (eps>0-><{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}>x2*x2+x3*x3 < eps*eps)".asFormula

    val energy = "\\forall eps (eps>0-><{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}>I1()*x1^2+I2()*x2^2+I3()*x3^2 < eps*eps)".asFormula

    val pr = proveBy(Imply(Gamma, energy),
      implyR(1) & allR(1) & implyR(1) &
        ODELiveness.dV(None)(1) <(
          QE,
          // Prove that solutions are trapped in I1() * x1^2 + I2() * x2^2 + I3() * x3^2 <= old()
          cutR("\\exists r (I1() * x1^2 + I2() * x2^2 + I3() * x3^2 = r)".asFormula)(1) <(
            QE,
            implyR(1) & existsL('Llast) &
            ODELiveness.compatCut("x2*x2+x1*x1+x3*x3<=r/I3()".asFormula)(1) <(skip , hideR(1) &
              dC("I1() * x1^2 + I2() * x2^2 + I3() * x3^2 <= r".asFormula)(1) <(
                ODE(1),
                ODE(1)
              ))
          ) &
          ODELiveness.odeReduce(true,"x2*x2+x1*x1+x3*x3<=r/I3()".asFormula::Nil)(1) &
          cohideR(1) & byUS(Ax.TExgt)
        )
    )

    // Lyapunov function 1/2*((I1()-I2())/I3() *x2^2 - (I3()-I1())/I2()*x3^2)
    // Picking tau = eps
    val pr11 = proveBy(Imply(Gamma,stable1),
      unfoldProgramNormalize &
        cutR(("\\exists k (" +
          "\\exists del (del > 0 & del < eps & \\forall x2 \\forall x3 (x2*x2+x3*x3 < del*del -> 1/2*((I1()-I2())/I3() *x2^2 - (I3()-I1())/I2()*x3^2)  < k)) &" +
          "\\forall x2 \\forall x3 (x2*x2+x3*x3 = eps*eps -> 1/2*((I1()-I2())/I3() *x2^2 - (I3()-I1())/I2()*x3^2) >= k))").asFormula)(1) <(
          QE,
          unfoldProgramNormalize &
            existsR("del".asTerm)(1) & andR(1) <(
            prop,
            unfoldProgramNormalize &
              allL(-11) & allL(-11) & implyL(-11) <(
              hideR(1) & prop,
              // Move the forall quantified antecedent into domain constraint
              // TODO: make tactic that adds universals directly into domain (without the universals)
              dC("x2*x2+x3*x3 = eps*eps -> 1/2*((I1()-I2())/I3() *x2^2 - (I3()-I1())/I2()*x3^2) >= k".asFormula)(1) <(
                hideL(-8) &
                  // This part is slightly simpler without having to close over the sub-domain
                  dC("1/2*((I1()-I2())/I3() *x2^2 - (I3()-I1())/I2()*x3^2)  < k".asFormula)(1) <(
                    ODE(1),
                    ODE(1)
                  )
                ,
                dWPlus(1) & allL(-8) & allL(-8) & prop
              )
            )
          )
        )
    )

    // The important direction of SAttr
    val pr12 = proveBy(
      Imply(And(stable1,gattractives1), gattractive1),
      implyR(1) & andL(-1) & allR(1) & implyR(1) &
        allL(-1) & implyL(-1) <(
        prop,
        existsL(-1) & allL("del".asTerm)(-1) &
          implyL(-1) <(
            prop,
            ODELiveness.kDomainDiamond("x2*x2+x3*x3 < del*del".asFormula)(1) <(
              prop,
              andL('Llast) &
                // Move the forall quantified antecedent into domain constraint
                // TODO: make tactic that adds universals directly into domain (without the universals)
                dC("(x2*x2+x3*x3 < del*del->[{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}]x2*x2+x3*x3 < eps*eps)".asFormula)(1) <(
                  dW(1) & prop,
                  dWPlus(1) & allL(-3) & allL(-3) & allL(-3) & close
                )
            )
          )
      )
    )

    val pr13 = proveBy(Imply(Gamma,gattractives1),
      implyR(1) &
        cutR(energy)(1) <(
          implyRi & byUS(pr),
          implyR(1) & allR(1) & implyR(1) &
            allL("eps*(I3()^(1/2))".asTerm)(-2) &
            implyL(-2) <(
              hideR(1) & QE,
              ODELiveness.kDomainDiamond("I1()*x1^2+I2()*x2^2+I3()*x3^2 < eps*(I3())^(1/2)*(eps*(I3())^(1/2))".asFormula)(1) <(
                close,
                dW(1) & QE
              )
            )
        )
    )

    // Propositional manipulation
    val pr14 = proveBy( Imply(Gamma, And(stable1 , gattractive1)),
      implyR(1) & cutR( And(stable1 , Imply(stable1,gattractive1)) )(1) <(
        andR(1) <(
          implyRi & byUS(pr11),
          implyR(1) & cutR(And(stable1,gattractives1))(1) <(
            andR(1) <(prop,
              implyRi & cohideR(1) & byUS(pr13)),
            cohideR(1) & byUS(pr12)
          )
        ),
        prop
      )
    )

    val stable2 = "\\forall eps (eps>0->\\exists del (del>0&\\forall x1 \\forall x2 \\forall x3 (x1*x1+x2*x2 < del*del->[{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}]x1*x1+x2*x2 < eps*eps)))".asFormula
    //Globally attractive
    val gattractive2 = "\\forall eps (eps>0-><{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}>[{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}]x1*x1+x2*x2 < eps*eps)".asFormula
    //Globally attractive (with stability)
    val gattractives2 = "\\forall eps (eps>0-><{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}>x1*x1+x2*x2 < eps*eps)".asFormula

    // Lyapunov function 1/2*(-(I3()-I1())/I2()*x1^2 + (I2()-I3())/I1() *x2^2)
    // Picking tau = eps
    val pr21 = proveBy(Imply(Gamma,stable2),
      unfoldProgramNormalize &
        cutR(("\\exists k (" +
          "\\exists del (del > 0 & del < eps & \\forall x1 \\forall x2 (x1*x1+x2*x2 < del*del -> 1/2*(-(I3()-I1())/I2()*x1^2 + (I2()-I3())/I1() *x2^2) < k)) &" +
          "\\forall x1 \\forall x2 (x1*x1+x2*x2 = eps*eps -> 1/2*(-(I3()-I1())/I2()*x1^2 + (I2()-I3())/I1() *x2^2) >= k))").asFormula)(1) <(
          QE,
          unfoldProgramNormalize &
            existsR("del".asTerm)(1) & andR(1) <(
            prop,
            unfoldProgramNormalize &
              allL(-11) & allL(-11) & implyL(-11) <(
              hideR(1) & prop,
              // Move the forall quantified antecedent into domain constraint
              // TODO: make tactic that adds universals directly into domain (without the universals)
              dC("x1*x1+x2*x2 = eps*eps -> 1/2*(-(I3()-I1())/I2()*x1^2 + (I2()-I3())/I1() *x2^2) >= k".asFormula)(1) <(
                hideL(-8) &
                  // This part is slightly simpler without having to close over the sub-domain
                  dC("1/2*(-(I3()-I1())/I2()*x1^2 + (I2()-I3())/I1() *x2^2) < k".asFormula)(1) <(
                    ODE(1),
                    ODE(1)
                  )
                ,
                dWPlus(1) & allL(-8) & allL(-8) & prop
              )
            )
          )
        )
    )

    // The important direction of SAttr
    val pr22 = proveBy(
      Imply(And(stable2,gattractives2),gattractive2),
      implyR(1) & andL(-1) & allR(1) & implyR(1) &
        allL(-1) & implyL(-1) <(
        prop,
        existsL(-1) & allL("del".asTerm)(-1) &
          implyL(-1) <(
            prop,
            ODELiveness.kDomainDiamond("x1*x1+x2*x2 < del*del".asFormula)(1) <(
              prop,
              andL('Llast) &
                // Move the forall quantified antecedent into domain constraint
                // TODO: make tactic that adds universals directly into domain (without the universals)
                dC("(x1*x1+x2*x2 < del*del->[{x1'=(I2()-I3())/I1()*x2*x3-a1()*x1,x2'=(I3()-I1())/I2()*x3*x1-a2()*x2,x3'=(I1()-I2())/I3()*x1*x2-a3()*x3&true}]x1*x1+x2*x2 < eps*eps)".asFormula)(1) <(
                  dW(1) & prop,
                  dWPlus(1) & allL(-3) & allL(-3) & allL(-3) & close
                )
            )
          )
      )
    )

    val pr23 = proveBy(Imply(Gamma,gattractives2),
      implyR(1) &
        cutR(energy)(1) <(
          implyRi & byUS(pr),
          implyR(1) & allR(1) & implyR(1) &
            allL("eps*(I3()^(1/2))".asTerm)(-2) &
            implyL(-2) <(
              hideR(1) & QE,
              ODELiveness.kDomainDiamond("I1()*x1^2+I2()*x2^2+I3()*x3^2 < eps*(I3())^(1/2)*(eps*(I3())^(1/2))".asFormula)(1) <(
                close,
                dW(1) & QE
              )
            )
        )
    )

    // Propositional manipulation
    val pr24 = proveBy( Imply(Gamma, And(stable2 , gattractive2)),
      implyR(1) & cutR( And(stable2 , Imply(stable2,gattractive2)) )(1) <(
        andR(1) <(
          implyRi & byUS(pr21),
          implyR(1) & cutR(And(stable2,gattractives2))(1) <(
            andR(1) <(prop,
              implyRi & cohideR(1) & byUS(pr23)),
            cohideR(1) & byUS(pr22)
          )
        ),
        prop
      )
    )

    println(pr14)
    println(pr24)
    pr14 shouldBe 'proved
    pr24 shouldBe 'proved
  }

  it should "prove epsilon stability for Moore-Greitzer Jet Engine" in withMathematica { _ =>
    val ode = "x1'=-x2-3/2*x1^2-1/2*x1^3, x2'=3*x1-x2".asDifferentialProgram
    // epsilon-stability bound-renamed to tau here
    // where tau = 10^-10

    val stable = "\\forall eps (eps>0->\\exists del (del>0&\\forall x1 \\forall x2 (x1*x1+x2*x2 < del*del->[{x1'=-x2-3/2*x1^2-1/2*x1^3,x2'=3*x1-x2&true}]x1*x1+x2*x2 < (tau+eps)*(tau+eps))))".asFormula

    val lyapstr = "x2 * (31.294269 * x2 - 9.7437617 * x1 - 18.856765 * x1 * x2 +\n      22.509931 * (x1 ^ 2) + 11.165278 * (x2 ^ 2)) -\n1.0 * x1 *\n    (9.7437617 * x2 - 100.0 * x1 - 48.132286 * x1 * x2 +\n     60.459815 * (x1 ^ 2) + 12.035111 * (x2 ^ 2)) +\n(x1 ^ 2) * (22.509931 * x2 - 60.459815 * x1 - 88.160775 * x1 * x2 +\n            100.0 * (x1 ^ 2) + 31.337433 * (x2 ^ 2)) +\n(x2 ^ 2) * (11.165278 * x2 - 12.035111 * x1 - 27.051686 * x1 * x2 +\n            31.337433 * (x1 ^ 2) + 14.189252 * (x2 ^ 2)) -\n1.0 * x1 * x2 *\n    (18.856765 * x2 - 48.132286 * x1 - 81.481369 * x1 * x2 +\n     88.160775 * (x1 ^ 2) + 27.051686 * (x2 ^ 2))"
    // Lyapunov function
    //      x2 * (31.294269 * x2 - 9.7437617 * x1 - 18.856765 * x1 * x2 +
    //            22.509931 * (x1 ^ 2) + 11.165278 * (x2 ^ 2)) -
    //      1.0 * x1 *
    //          (9.7437617 * x2 - 100.0 * x1 - 48.132286 * x1 * x2 +
    //           60.459815 * (x1 ^ 2) + 12.035111 * (x2 ^ 2)) +
    //      (x1 ^ 2) * (22.509931 * x2 - 60.459815 * x1 - 88.160775 * x1 * x2 +
    //                  100.0 * (x1 ^ 2) + 31.337433 * (x2 ^ 2)) +
    //      (x2 ^ 2) * (11.165278 * x2 - 12.035111 * x1 - 27.051686 * x1 * x2 +
    //                  31.337433 * (x1 ^ 2) + 14.189252 * (x2 ^ 2)) -
    //      1.0 * x1 * x2 *
    //          (18.856765 * x2 - 48.132286 * x1 - 81.481369 * x1 * x2 +
    //           88.160775 * (x1 ^ 2) + 27.051686 * (x2 ^ 2))

    val pr1 = proveBy(Imply("tau = 10^-10".asFormula,stable),
      unfoldProgramNormalize&
        //On ||x||=eps+tau, there is a global lower bound k > 0 on the Lyapunov function
        //From paper, this bound can be k = alpha = 2.95 * 10^-19
        cutR(s"\\forall x1 \\forall x2 (x1*x1+x2*x2 = (eps+tau)*(eps+tau) -> $lyapstr >= 2.95 * 10^-19)".asFormula)(1) <(
          QE,
          unfoldProgramNormalize &
            //There is del s.t. ||x||<del -> v < k
            //From paper, this del can be del = eps' = 5*10^-11
            cutR(s"\\exists del (del > 0 & del < eps+tau & \\forall x1 \\forall x2 (x1*x1+x2*x2 < del*del -> $lyapstr < 2.95 * 10^-19))".asFormula)(1) <(
              hideL('Llast) & QE,
              unfoldProgramNormalize &
                existsR("del".asTerm)(1) & andR(1) <(
                prop,
                unfoldProgramNormalize &
                allL(-6) & allL(-6) & //x1, x2
                implyL(-6) <(
                  hideR(1) & prop,
                  // Move the forall quantified antecedent into domain constraint
                  // TODO: make tactic that adds universals directly into domain (without the universals)
                  dC(s"(x1*x1+x2*x2=(eps+tau)*(eps+tau)->$lyapstr >= 2.95 * 10^-19) & $lyapstr < 2.95 * 10^-19".asFormula)(1) <(
                    hideL(-3) & ODE(1)
                    ,
                    boxAnd(1) & andR(1) <(
                      dWPlus(1) & allL(-3) & allL(-3) & prop,
                      hideL(-3) & ODE(1)
                    )
                  )
                )
              )
            )
        )
    )

    println(pr1)
    pr1 shouldBe 'proved
  }

  it should "prove 3rd order stability for pendulum" in withMathematica { _ =>
    val ode = "theta' = w, w'= -a*(theta - theta^3/6) - b*w".asDifferentialProgram
    val stable = stabODE(ode)
    val attractive = attrODE(ode)

    val lyap = "a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4".asTerm
    val lie = DifferentialHelper.simplifiedLieDerivative(ode,lyap, ToolProvider.simplifierTool())
    println(lie)

//    val qe = proveBy("==> \\exists theta0 \\exists w0 ( (theta0*theta0+w0*w0 <= 2*2)&theta0*theta0+w0*w0 >= 1*1&\\forall theta \\forall w ((theta*theta+w*w <= 2*2)&theta*theta+w*w >= 1*1->-(a*(2*theta*w)*2/4+(2*(b*theta+w)*(b*w+(-a*(theta-theta^3/6)-b*w))+2*w*(-a*(theta-theta^3/6)-b*w))*4/16)>=-(a*(2*theta0*w0)*2/4+(2*(b*theta0+w0)*(b*w0+(-a*(theta0-theta0^3/6)-b*w0))+2*w0*(-a*(theta0-theta0^3/6)-b*w0))*4/16)))".asSequent,
//      QE)
//    println(qe)

    val pr1 = proveBy(Imply("a > 0 & b > 0".asFormula,stable),
      unfoldProgramNormalize &
      cutR("\\exists tau (tau > 0 & tau < eps & \\forall theta \\forall w (theta*theta+w*w <= tau*tau -> 1/12*((-6)*b*w^2+a*theta^2*(b*((-6)+theta^2)+2*theta*w)) <= 0))".asFormula)(1) <(
        QE,
        unfoldProgramNormalize &
        //On ||x||=tau, there is a global lower bound on k
        cutR("\\exists k (k > 0 & \\forall theta \\forall w (theta*theta+w*w = tau*tau -> a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 >= k))".asFormula)(1) <(
          hideL('Llast) & QE,
          unfoldProgramNormalize &
          //There is del s.t. ||x||<del -> v < k
          cutR("\\exists del (del > 0 & del < tau & \\forall theta \\forall w (theta*theta+w*w < del*del -> a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 < k))".asFormula)(1) <(
            hideL('Llast) & hideL(-6) & QE,
            unfoldProgramNormalize &
            existsR("del".asTerm)(1) & andR(1) <(
              prop,
              unfoldProgramNormalize &
              allL(-11) & allL(-11) & //theta, w
              implyL(-11) <(
                hideR(1) & prop,
                generalize("theta*theta+w*w < tau*tau".asFormula)(1) <(
                  hideL(-5) & hideL(-3) &
                  ODEInvariance.dCClosure(1) <(
                    hideL(-6) & hideL(-4) & QE,
                    dC("theta*theta+w*w=tau*tau->a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4>=k".asFormula)(1) <(
                      hideL(-6) &
                      dC("1/12*((-6)*b*w^2+a*theta^2*(b*((-6)+theta^2)+2*theta*w))<=0".asFormula)(1) <(
                        hideL(-4) &
                          dC("a*(theta^2)/2 + ((b*theta+w)^2+w^2)/4 < k".asFormula)(1) <(
                            ODE(1),
                            ODE(1)
                          ),
                        dWPlus(1) & allL(-4) & allL(-4) & QE
                      )
                      ,
                      dWPlus(1) & allL(-6) & allL(-6) & prop
                    )
                  ),
                  QE
                )
              )
            )
          )
        )
      )
    )

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
