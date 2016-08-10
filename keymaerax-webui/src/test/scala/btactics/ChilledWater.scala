/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, OnAll, PosInExpr, TheType}
import edu.cmu.cs.ls.keymaerax.bellerophon.Find._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Box, Imply}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.language.postfixOps

/**
  * Chilled water system case study.
  */
@SlowTest
class ChilledWater extends TacticTestBase {

  "Model 0" should "be provable" in withMathematica { implicit qeTool =>
    //val s = KeYmaeraXProblemParser(scala.io.Source.fromFile("/Users/smitsch/Downloads/chilled-m0.kyx").getLines().mkString)
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/chilledwater/chilled-m0.kyx"))
    val inv = """(Tw < Tl) &
                |    (Tl < Tlu() &
                |    a() <= Tw &                  /* needed for DA in model branch v:=1;Tw:=a() */
                |    (l=1 -> v=1) &              /* If the load is on, the valve is open.        */
                |    (v=0 -> l=0) &              /* If the valve is closed, the load is off.     */
                |    (l=0 | l=1) &
                |    (v=1 | v=0) &
                |    (v=1 -> Tw=a()))""".stripMargin.asFormula

    val specialNormalize = normalize(andR('R), step('L), step('R))

    def DAcleanup(msg: String): BelleExpr = skip <(
      printIndexed(msg + "b4 QE") & QE & done,
      // Formula of the form lhs -> rhs, 1::Nil traverses to rhs
      printIndexed(msg + "b4 diffInd") & diffInd(qeTool)(1, 1::Nil) & QE() & done
    )

    def DAy(msg: String) = DifferentialTactics.Dconstify(
      DA("{y'=(r()/2)*y+0}".asDifferentialProgram,
        "y^2*(Tl - Tw) = 1".asFormula)(1)
    )(1) & DAcleanup(msg) & done

    val twLessTl = printIndexed("case split on l and v") <(
      /*v:=1;Tw:=a()*/ orL(FindL(0, Some("l=0|l=1".asFormula))) <(
      /* l=0 */exhaustiveEqL2R(FindL(0, Some("l=0".asFormula))) & DAy("After DA (l=0)") & done
      ,
      /* l=1 */ exhaustiveEqL2R(FindL(0, Some("l=1".asFormula))) &
      DA("{y'=(r()/2)*y+0}".asDifferentialProgram,
        "(Tl-Tw)*y^2>0".asFormula)(1) & DAcleanup("After DA (l=1)") & done
      ),
      /* l=0 */ exhaustiveEqL2R(FindL(0, Some("l=0".asFormula))) &
      DA("{y'=r()*y+0}".asDifferentialProgram,
        "(Tl-Tw)*y^2>0".asFormula)(1) & DAcleanup("After DA (l=0 and v=0)") & done,
      /* v=1 */ exhaustiveEqL2R(FindL(0, Some("v=1".asFormula))) &
      DA("{y'=(r()/2)*y+0}".asDifferentialProgram,
        "(Tl-Tw)*y^2>0".asFormula)(1) & DAcleanup("After DA (v=1 and l=1)") & done,
      // split v=0 | v=1 and use y'=r()/2*y DA in v=1 and y'=r()*y in v=0 case
      orL(FindL(0, Some("v=1|v=0".asFormula))) <(
        DA("{y'=(r()/2)*y+0}".asDifferentialProgram,
          "(Tl-Tw)*y^2>0".asFormula)(1) & DAcleanup("After DA (v=1 and l=1)") & done,
        DA("{y'=r()*y+0}".asDifferentialProgram,
          "(Tl-Tw)*y^2>0".asFormula)(1) & DAcleanup("After DA (l=0 and v=0)") & done
        )
      )

    val tlLessTlu = chase(1) & specialNormalize <(
      /* v:=1;Tw:=a() */
      diffInvariant("Tw=a()".asFormula)(1) &
        DA("{y'=(r()/2)*y+0}".asDifferentialProgram, "(Tlu()-Tl)*y^2>0".asFormula)(1) & DAcleanup("Tl<Tlu After DA (v=1 and l=1)") & done,
      /* ?l=0;v:=0; */
      diffCut("Tw<Tl".asFormula)(1) <(
        /* use cut */ diffInd(qeTool)(1) & done,
        /* show cut */ DA("{y'=r()*y+0}".asDifferentialProgram,
        "(Tl-Tw)*y^2>0".asFormula)(1) & DAcleanup("Tl<Tlu After DA (l=0 and v=0)") & done
        ),
      /* ?v=1;l:=0; */
      diffInvariant("Tw=a()".asFormula)(1) &
        DA("{y'=(r()/2)*y+0}".asDifferentialProgram, "(Tlu()-Tl)*y^2>0".asFormula)(1) & DAcleanup("Tl<Tlu After DA (v=1 and l=1)") & done,
      /* l:=0; */
      orL(FindL(0, Some("v=1|v=0".asFormula))) <(
        /* v=1 */
        diffInvariant("Tw=a()".asFormula)(1) &
          DA("{y'=(r()/2)*y+0}".asDifferentialProgram, "(Tlu()-Tl)*y^2>0".asFormula)(1) & DAcleanup("Tl<Tlu After DA (v=1 and l=1)") & done,
        /* v=0 */
        diffCut("Tw<Tl".asFormula)(1) <(
          /* use cut */ diffInd(qeTool)(1) & done,
          /* show cut */ DA("{y'=r()*y+0}".asDifferentialProgram,
          "(Tl-Tw)*y^2>0".asFormula)(1) & DAcleanup("Tl<Tlu After DA (l=0 and v=0)") & done
          )
        )
      )

    val aLessTw = chase(1) & specialNormalize <(
      diffCut("Tw=a()".asFormula, "Tw<Tl".asFormula)(1) <(
        diffWeaken(1) & QE & done,
        printIndexed("B2") & diffInd(qeTool)(1) & done,
        printIndexed("B3") & skip /* leave open for subsequent call to twLessTl */
        ),
      diffCut("Tw<Tl".asFormula, "a()<=Tw".asFormula)(1) <(
        diffWeaken(1) & QE & done,
        skip, /* leave open for subsequent call to twLessTl */
        printIndexed("C1.1") & diffInd(qeTool)(1) & done
        ),
      diffCut("Tw=a()".asFormula, "Tw<Tl".asFormula)(1) <(
        printIndexed("C2.1") & diffWeaken(1) & QE & done,
        printIndexed("C2.2") & diffInd(qeTool)(1) & done,
        printIndexed("C2.3") & skip /* leave open for subsequent call to twLessTl */
        ),
      diffCut("Tw<Tl".asFormula, "a()<=Tw".asFormula)(1) <(
        diffWeaken(1) & QE & done,
        skip, /* leave open for subsequent call to twLessTl */
        printIndexed("C3.1") & diffInd(qeTool)(1) & done
        )
      ) & twLessTl & done

    val propRest = chase(1) & specialNormalize <(
      diffInvariant("Tw=a()".asFormula)(1),
      skip,
      diffInvariant("Tw=a()".asFormula)(1),
      orL(FindL(0, Some("v=1|v=0".asFormula))) <(
        diffInvariant("Tw=a()".asFormula)(1),
        skip
        )
      ) & OnAll(diffWeaken(1) & QE) & done

    val tactic = implyR('_) & andL('_)*@ TheType() & printIndexed("implyR then andL") & loop(inv)(1) & printIndexed("After loop") <(
      QE & done,
      QE & done,
      boxAnd(1) & andR(1) <(
        /* Tw < Tl */
        chase(1) & specialNormalize & twLessTl & done,
        boxAnd(1) & andR(1) <(
          /* Tl < Tlu() */
          tlLessTlu & done,
          boxAnd(1) & andR(1) <(
            /* a() <= Tw */
            aLessTw & done,
            /* all the propositional minutia */
            propRest & done
            )
          )
        )
      )

    proveBy(s, tactic) shouldBe 'proved
  }

}

