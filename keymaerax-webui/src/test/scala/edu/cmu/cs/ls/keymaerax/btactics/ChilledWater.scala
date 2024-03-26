/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.Find._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.printIndexed
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.testhelper.ParserFactory._

import scala.language.postfixOps

/** Chilled water system case study. */
@SlowTest
class ChilledWater extends TacticTestBase {

  def DAcleanup(msg: String): BelleExpr =
    /* induction: diff*y^2>0 -> [{ode}]diff*y^2>0 */ printIndexed(msg + "b4 diffInd") & dI()(1, 0 :: Nil) & QE &
      done // formula of the form \exists rhs, 0::Nil traverses to rhs

  /* DA depending on the states of valve and load, diff is what we're trying to prove is
     positive (e.g., Tl-Tw) */
  def DAchilled(valve: Boolean, load: Option[Boolean], diff: String): BelleExpr =
    ((valve, load) match {
      case (true, _) => dG("{y'=(r()/2)*y+0}".asDifferentialProgram, Some(s"($diff)*y^2>0".asFormula))(1)
      case (false, Some(false)) => dG("{y'=r()*y+0}".asDifferentialProgram, Some(s"($diff)*y^2>0".asFormula))(1)
      case (false, Some(true)) => dG("{y'=r()*y+0}".asDifferentialProgram, Some(s"($diff)*y^2>0".asFormula))(1)
      // no other case expected to occur
    }) & DAcleanup(s"After DA (load=$load, valve=$valve, diff=$diff)")

  /* Case [ctrl;ode]Tw<Tl */
  def twLessTl: BelleExpr = printIndexed("case split on model non-det. choices") <
    (
      /*v:=1;Tw:=a()*/ DAchilled(valve = true, load = None, "Tl-Tw") & done,
      /* ?l=0;v:=0; */ DAchilled(valve = false, load = Some(false), "Tl-Tw") & done,
      /* ?v=1;l:=1; */ DAchilled(valve = true, load = Some(true), "Tl-Tw") & done,
      /* l:=0; split v=1|v=0 */
      orL(FindLPlain("v=1|v=0".asFormula)) <
        (
          /* v=1 */ DAchilled(valve = true, load = Some(false), "Tl-Tw") & done,
          /* v=0 */ DAchilled(valve = false, load = Some(false), "Tl-Tw") & done,
        ),
    )

  /* Case [ctrl;ode]Tl<Tlu(), reduces to Tw<Tl whenever possible */
  def tlLessTlu: BelleExpr = printIndexed("case split on model non-det. choices") <
    (
      /* v:=1;Tw:=a(), here we need to actually exploit h()/r()+a()<Tlu() */
      diffInvariant("Tw=a()".asFormula)(1) & DAchilled(valve = true, load = None, "Tlu()-Tl") & done,
      /* ?l=0;v:=0; */
      dC("Tw<Tl".asFormula)(1) <
        (
          /* use cut */ dI()(1) & done,
          /* show cut */ DAchilled(valve = false, load = Some(false), "Tl-Tw") &
            done, // @note now we know sign of Tl' plus Tl<Tlu initially
        ),
      /* ?v=1;l:=0; */
      diffInvariant("Tw=a()".asFormula)(1) & DAchilled(valve = true, load = Some(false), "Tlu()-Tl") & done,
      /* l:=0; */
      orL(FindLPlain("v=1|v=0".asFormula)) <
        (
          /* v=1 */
          diffInvariant("Tw=a()".asFormula)(1) & DAchilled(valve = true, load = Some(false), "Tlu()-Tl") & done,
          /* v=0 */
          dC("Tw<Tl".asFormula)(1) <
            (
              /* use cut */ dI()(1) & done,
              /* show cut */ DAchilled(valve = false, load = Some(false), "Tl-Tw") & done,
            ),
        ),
    )

  /* Case [ctrl;ode]a()<=Tw */
  def aLessEqualTw: BelleExpr = skip <
    (
      /* v:=1;Tw:=a; */ diffInvariant("Tw=a()".asFormula)(1) & dW(1) & QE & done,
      /* ?l=0;v:=0; */ dC("Tw<Tl".asFormula :: "a()<=Tw".asFormula :: Nil)(1) <
        (dW(1) & QE & done, DAchilled(valve = false, load = Some(false), "Tl-Tw") & done, dI()(1) & done),
      /* ?v=1;l:=1; */ diffInvariant("Tw=a()".asFormula)(1) & dW(1) & QE & done,
      /* l:=0; */ dC("Tw<Tl".asFormula :: "a()<=Tw".asFormula :: Nil)(1) <
        (
          dW(1) & QE & done,
          orL(FindLPlain("v=1|v=0".asFormula)) <
            (
              DAchilled(valve = true, load = Some(false), "Tl-Tw") & done,
              DAchilled(valve = false, load = Some(false), "Tl-Tw") & done,
            ),
          dI()(1) & done,
        ),
    )

  def propRest: BelleExpr = skip <
    (
      diffInvariant("Tw=a()".asFormula)(1),
      skip, // @note evolution domain already strong enough without additional diff. cut
      diffInvariant("Tw=a()".asFormula)(1),
      orL(FindLPlain("v=1|v=0".asFormula)) <
        (
          diffInvariant("Tw=a()".asFormula)(1),
          skip, // @note evolution domain already strong enough without additional diff. cut
        ),
    ) & OnAll(dW(1) & QE) & done

  "Model 0" should "be provable" in withMathematica { _ =>
    // val s = KeYmaeraXProblemParser(scala.io.Source.fromFile("/path/to/file").getLines().mkString)
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/chilledwater/chilled-m0.kyx"))
    val inv = """(Tw < Tl) &
                |    (Tl < Tlu() &
                |    a() <= Tw &                  /* needed for DA in model branch v:=1;Tw:=a() */
                |    (l=1 -> v=1) &              /* If the load is on, the valve is open.        */
                |    (v=0 -> l=0) &              /* If the valve is closed, the load is off.     */
                |    (l=0 | l=1) &
                |    (v=1 | v=0) &
                |    (v=1 -> Tw=a()))""".stripMargin.asFormula

    val tactic = implyR(Symbol("_")) & SaturateTactic(andL(Symbol("_"))) & printIndexed("implyR then andL") &
      loop(inv)(1) &
      printIndexed("After loop") <
      (
        QE & done,
        QE & done,
        boxAnd(1) &
          andR(1) <
          (
            /* Tw < Tl */
            chase(1) & unfoldProgramNormalize & twLessTl & done,
            boxAnd(1) &
              andR(1) <
              (
                /* Tl < Tlu() */
                chase(1) & unfoldProgramNormalize & tlLessTlu & done,
                boxAnd(1) &
                  andR(1) <
                  (
                    /* a() <= Tw */
                    chase(1) & unfoldProgramNormalize & aLessEqualTw & done,
                    /* all the propositional minutia */
                    chase(1) & unfoldProgramNormalize & propRest & done,
                  ),
              ),
          ),
      )

    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  it should "be provable with ODE" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/chilledwater/chilled-m0.kyx"))
    val inv = """(Tw < Tl) &
                |    (Tl < Tlu() &
                |    a() <= Tw &                  /* needed for DA in model branch v:=1;Tw:=a() */
                |    (l=1 -> v=1) &              /* If the load is on, the valve is open.        */
                |    (v=0 -> l=0) &              /* If the valve is closed, the load is off.     */
                |    (l=0 | l=1) &
                |    (v=1 | v=0) &
                |    (v=1 -> Tw=a()))""".stripMargin.asFormula

    val odeTlLessTlu = printIndexed("case split on model non-det. choices") <
      (
        /* v:=1;Tw:=a(), here we need to actually exploit h()/r()+a()<Tlu() */
        skip,
        /* ?l=0;v:=0; */
        dC("Tw<Tl".asFormula)(1), // @note now we know sign of Tl' plus Tl<Tlu initially
        /* ?v=1;l:=0; */
        dC("Tw=a()".asFormula)(1),
        /* l:=0; */
        orL(FindLPlain("v=1|v=0".asFormula)) <
          (
            /* v=1 */
            dC("Tw=a()".asFormula)(1),
            /* v=0 */
            dC("Tw<Tl".asFormula)(1),
          ),
      ) & OnAll(ODE(Symbol("R"))) & done

    val odeALessEqualTw = skip <
      (
        /* v:=1;Tw:=a; */ dC("Tw=a()".asFormula)(1),
        /* ?l=0;v:=0; */ dC("Tw<Tl".asFormula :: "a()<=Tw".asFormula :: Nil)(1),
        /* ?v=1;l:=1; */ dC("Tw=a()".asFormula)(1),
        /* l:=0; */ dC("Tw<Tl".asFormula :: "a()<=Tw".asFormula :: Nil)(1) <
          (skip, orL(FindLPlain("v=1|v=0".asFormula)), skip),
      ) & OnAll(ODE(Symbol("R"))) & done

    // @note and once again
    val odePropRest = skip <
      (
        dC("Tw=a()".asFormula)(1),
        skip, // @note evolution domain already strong enough without additional diff. cut
        dC("Tw=a()".asFormula)(1),
        orL(FindLPlain("v=1|v=0".asFormula)) <
          (
            dC("Tw=a()".asFormula)(1),
            skip, // @note evolution domain already strong enough without additional diff. cut
          ),
      ) & OnAll(ODE(Symbol("R"))) & done

    val tactic = implyR(Symbol("_")) & SaturateTactic(andL(Symbol("_"))) & printIndexed("implyR then andL") &
      loop(inv)(1) &
      printIndexed("After loop") <
      (
        QE & done,
        QE & done,
        boxAnd(1) &
          andR(1) <
          (
            /* Tw < Tl */
            chase(1) & unfoldProgramNormalize & OnAll(ODE(Symbol("R"))) /* twLessTl */ & done,
            boxAnd(1) &
              andR(1) <
              (
                /* Tl < Tlu() */
                chase(1) & unfoldProgramNormalize & odeTlLessTlu & done,
                boxAnd(1) &
                  andR(1) <
                  (
                    /* a() <= Tw */
                    chase(1) & unfoldProgramNormalize & odeALessEqualTw & done,
                    /* all the propositional minutia */
                    chase(1) & unfoldProgramNormalize & odePropRest & done,
                  ),
              ),
          ),
      )

    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  "Model 1" should "be provable" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/chilledwater/chilled-m1.kyx"))
    val inv = """(Tw < Tl) &
                |    (Tl < Tlu() &
                |    a() <= Tw &                  /* needed for DA in model branch v:=1;Tw:=a() */
                |    (l=0 | l=1) &
                |    (v=1 | v=0) &
                |    (v=1 -> Tw=a()))""".stripMargin.asFormula

    val tactic = implyR(Symbol("_")) & SaturateTactic(andL(Symbol("_"))) & printIndexed("implyR then andL") &
      loop(inv)(1) &
      printIndexed("After loop") <
      (
        QE & done,
        QE & done,
        // reduce the proof to the proof of Model 0
        boxAnd(1) &
          andR(1) <
          (
            /* Tw < Tl */
            chase(1) &
              unfoldProgramNormalize <
              (
                skip,
                skip,
                /* new branch */
                dC("Tw<Tl".asFormula)(1) <
                  (
                    /* use cut */ dW(1) & QE & done,
                    /* show cut */ DAchilled(valve = false, load = Some(true), "Tl-Tw") & done,
                  ) & done,
                skip,
                skip,
              ) & twLessTl & done,
            boxAnd(1) &
              andR(1) <
              (
                /* Tl < Tlu() */
                chase(1) &
                  unfoldProgramNormalize <
                  (
                    skip,
                    skip,
                    /* new branch */
                    dC("Tw<Tl".asFormula)(1) <
                      (
                        /* use cut */ diffInvariant("Tl<Tlu()-h()*(e()-t)".asFormula)(1) & dW(1) & QE & done,
                        /* show cut */ DAchilled(valve = false, load = Some(true), "Tl-Tw") & done,
                      ) & done,
                    skip,
                    skip,
                  ) & tlLessTlu & done,
                boxAnd(1) &
                  andR(1) <
                  (
                    /* a() <= Tw */
                    chase(1) &
                      unfoldProgramNormalize <
                      (
                        skip,
                        skip,
                        /* new branch */
                        dC("Tw<Tl".asFormula :: "a()<=Tw".asFormula :: Nil)(1) <
                          (
                            dW(1) & QE & done,
                            DAchilled(valve = false, load = Some(true), "Tl-Tw") & done,
                            dI()(1) & done,
                          ),
                        skip,
                        skip,
                      ) & aLessEqualTw & done,
                    /* all the propositional minutia */
                    chase(1) &
                      unfoldProgramNormalize <
                      (
                        skip,
                        skip,
                        /* new branch */
                        dW(1) & QE & done,
                        skip,
                        skip,
                      ) & propRest & done,
                  ),
              ),
          ),
      )

    proveBy(s, tactic) shouldBe Symbol("proved")
  }

}
