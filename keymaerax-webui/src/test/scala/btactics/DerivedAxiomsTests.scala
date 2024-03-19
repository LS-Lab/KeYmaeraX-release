/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleProvable
import edu.cmu.cs.ls.keymaerax.btactics.Ax._
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.btactics.macros.{ProvableInfo, StorableInfo}
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tagobjects.OptimisticTest
import edu.cmu.cs.ls.keymaerax.tags.{CheckinTest, IgnoreInBuildTest, SummaryTest, UsualTest}

import java.io.{File, FileWriter, FilenameFilter}
import java.lang.reflect.InvocationTargetException
import scala.collection.immutable
import scala.reflect.runtime.{universe => ru}

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.Ax]]
 *
 * @see
 *   [[CodeNameChecker]]
 */
@CheckinTest @SummaryTest @UsualTest
@IgnoreInBuildTest // otherwise it deletes derived lemmas while other tests are running
class DerivedAxiomsTests extends TacticTestBase(registerAxTactics = None) {

  private def check(pi: => ProvableInfo): Sequent = {
    DerivationInfoRegistry.init(initLibrary = false)
    pi.provable shouldBe Symbol("proved")
    useToClose(pi)
    pi.provable.conclusion
  }

  private def useToClose(pi: ProvableInfo): Unit = {
    ProvableSig.startPlainProof(pi.provable.conclusion)(pi.provable, 0) shouldBe Symbol("proved")
    // @note same test as previous line, just to make sure the lemma can be used by substitution
    theInterpreter(
      TactixLibrary.byUS(pi),
      BelleProvable.plain(ProvableSig.startPlainProof(pi.provable.conclusion)),
    ) match {
      case BelleProvable(provable, _) => provable shouldBe Symbol("proved")
      case _ => fail()
    }
  }

  "Derived axioms and rules" should "prove one-by-one on a fresh lemma database" ignore
    withMathematica(
      initLibrary = false,
      testcode = { _ =>
        withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
          getDerivedAxiomsMirrors.foreach({ case (name, fm) =>
            // delete all stored lemmas
            LemmaDBFactory.lemmaDB.deleteDatabase()
            DerivationInfoRegistry.init(initLibrary = false)
            // re-initialize DerivedAxioms singleton object to forget lazy vals of previous iterations
            val c = Ax.getClass.getDeclaredConstructor()
            c.setAccessible(true)
            withClue(
              "Missing dependency in '" + name + "': inspect stack trace for occurrences of Axioms.scala for hints where to add missing dependency\n"
            ) {
              try { fm.bind(c.newInstance())() }
              catch { case ex: InvocationTargetException => throw ex.getTargetException }
            }
          })
        }
      },
    )

  // @todo derived rules do not need Mathematica

  "Derived Rule" should "prove allG" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      allGeneralize.provable.subgoals shouldBe List(
        Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("p_(||)".asFormula))
      )
    },
  )

  it should "prove Ind from FP" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      indrule.provable.subgoals shouldBe List(
        Sequent(immutable.IndexedSeq("p_(||)".asFormula), immutable.IndexedSeq("[a_;]p_(||)".asFormula))
      )
    },
  )

  it should "prove FP from Ind" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      FPruleduplicate.provable.subgoals shouldBe List(
        Sequent(immutable.IndexedSeq("p_(||) | <a_;>q_(||)".asFormula), immutable.IndexedSeq("q_(||)".asFormula)),
        Sequent(immutable.IndexedSeq("p_(||) | <a_;>q_(||)".asFormula), immutable.IndexedSeq("q_(||)".asFormula)),
      )
    },
  )

  it should "prove contra2" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      contraposition2Rule.provable.subgoals shouldBe List(
        Sequent(immutable.IndexedSeq("!q_(||)".asFormula), immutable.IndexedSeq("!p_(||)".asFormula))
      )
    },
  )

  it should "prove Goedel" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      Goedel.provable.subgoals shouldBe List(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("p_(||)".asFormula)))
    },
  )

  it should "prove CT" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      CTtermCongruence.provable.subgoals shouldBe List(
        Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("f_(||) = g_(||)".asFormula))
      )
    },
  )

  it should "prove [] monotone" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      monbaxiom.provable.subgoals shouldBe List(
        Sequent(immutable.IndexedSeq("p_(||)".asFormula), immutable.IndexedSeq("q_(||)".asFormula))
      )
    },
  )

  it should "prove [] monotone 2" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      monb2.provable.subgoals shouldBe List(
        Sequent(immutable.IndexedSeq("q_(||)".asFormula), immutable.IndexedSeq("p_(||)".asFormula))
      )
    },
  )

  it should "prove con convergence flat" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      conflat.provable.subgoals shouldBe List(
        // Sequent(immutable.IndexedSeq("v_<=0".asFormula, "J(||)".asFormula), immutable.IndexedSeq("p_(||)".asFormula)),
        Sequent(
          immutable.IndexedSeq("\\exists x_ (x_<=0 & J(||))".asFormula),
          immutable.IndexedSeq("p_(||)".asFormula),
        ),
        Sequent(
          immutable.IndexedSeq("x_>0".asFormula, "J(||)".asFormula),
          immutable.IndexedSeq("<a_{|x_|};><x_:=x_-1;>J(||)".asFormula),
        ),
      )
    },
  )

  "Semantically-renamed Derived Axioms" should "prove [:=] assign equality y" in { check(assignbeqy) }
  it should "prove [:=] self assign y" in { check(selfassignby) }
  it should "prove DE differential effect (system) y" in { check(DEsysy) }
  it should "prove all dual y" in { check(alldy) }
  it should "prove all dual time" in { check(alldt) }
  it should "prove all eliminate y" in { check(ally) }

  "Derived Axioms" should "prove <-> reflexive" in { check(equivReflexive) }
  it should "prove !!" in { check(doubleNegation) }
  it should "prove exists dual" in { check(existsDual) }
  it should "prove all eliminate" taggedAs OptimisticTest ignore { check(alle) }
  it should "prove exists eliminate" in { check(existse) }
  it should "prove exists eliminate y" in { check(existsey) }
  it should "prove !exists" in { check(notExists) }
  it should "prove !all" in { check(notAll) }
//  it should "prove !all2" in {check(notAll2)}
  it should "prove ![]" in { check(notBox) }
  it should "prove !<>" in { check(notDiamond) }
  it should "prove all distribute" in { check(allDist) }
  it should "prove all instantiate" in { check(allInst) }
  it should "prove all instantiate prime" in { check(allInstPrime) }
  it should "prove all then exists" in { check(allThenExists) }
  it should "prove all distribute elim" in { check(allDistElim) }
  it should "prove equiv expand" in { check(equivExpand) }
  it should "prove box dual" in { check(box) }
  it should "prove V vacuous" in { check(V) }
  it should "prove vacuous all quantifier" in { check(allV) }
//  it should "prove K1" in {check(K1)}
//  it should "prove K2" in {check(K2)}
  // @todo nrf it should "prove box split" in {check(boxAnd)}
//  it should "prove box split left" in {check(boxSplitLeft)}
//  it should "prove box split right" in {check(boxSplitRight)}
  it should "prove [] split" in { check(boxAnd) }
  it should "prove [] conditional split" in { check(boxImpliesAnd) }
  it should "prove <> split" in { check(diamondOr) }
  it should "prove []~><> propagation" in { check { boxDiamondPropagation } }
  it should "prove <:=> assign" in { check(assigndAxiom) }
//  it should "prove <:=> assign v" in {check(dummyassigndVvariant)}
  it should "prove := assign dual" in { check(assignDual) }
  it should "prove all substitute" in withMathematica(initLibrary = false, testcode = { _ => check(allSubstitute) })
  it should "prove [:=] equational" in { check(assignbequational) }
  it should "prove [:=] assign equality exists" in { check(assignbequalityexists) }
  it should "prove exists and" in { check(existsAnd) }
  it should "prove [:=] assign implies exists" in { check(assignbexists) }
  it should "prove <:=> assign equality" in { check(assigndEqualityAxiom) }
  it should "prove <:=> assign dual 2" in { check(assignDual2) }
  it should "prove <:=> assign equality all" in { check(assigndEqualityAll) }
  it should "prove [:=] vacuous assign" in { check(vacuousAssignb) }
  it should "prove <:=> vacuous assign" in { check(vacuousAssignd) }
  // @todo it should "prove [':=] differential assign" in {check(assignDAxiomb)}
  it should "prove <':=> differential assign" in { check(Dassignd) }
  it should "prove <:*> assign nondet" in { check(randomd) }
  it should "prove [y':=] differential assign 2" in { check(Dassignby) }
  it should "prove <?> test" in { check(testd) }
  it should "prove <++> choice" in { check(choiced) }
  it should "prove <;> compose" in { check(composed) }
  it should "prove <*> iterate" in { check(iterated) }
  it should "prove <*> approx" in { check(loopApproxd) }
  it should "prove [*] approx" in { check(loopApproxb) }
  it should "prove II induction" in { check(IIinduction) }
  it should "prove [*] merge" in { check(loopMergeb) }
  it should "prove <*> merge" in { check(loopMerged) }
  it should "prove [**] iterate iterate" in { check(iterateiterateb) }
  it should "prove <**> iterate iterate" in { check(iterateiterated) }
  it should "prove [*-] backiterate sufficiency" in { check(backiteratebsuff) }
  it should "prove [*-] backiterate necessity" in { check(backiteratebnecc) }
  it should "prove [*-] backiterate" in { check(backiterateb) }
  it should "prove Ieq induction" in { check(I) }
  it should "prove [d] dual" in { check(dualb) }
  it should "prove [d] dual direct" in { check(dualDirectb) }
  it should "prove <d> dual direct" in { check(dualDirectd) }
  it should "prove exists generalize" in { check(existsGeneralize) }
  it should "prove vacuous exists" in { check(existsV) }
  it should "prove V[:*] vacuous assign nondet" in { check(vacuousBoxAssignNondet) }
  it should "prove V<:*> vacuous assign nondet" in { check(vacuousDiamondAssignNondet) }
  it should "prove & commute" in { check(andCommute) }
  it should "prove & assoc" in { check(andAssoc) }
  it should "prove !& deMorgan" in { check(notAnd) }
  it should "prove !| deMorgan" in { check(notOr) }
  it should "prove !-> deMorgan" in { check(notImply) }
  it should "prove !<-> deMorgan" in { check(notEquiv) }
  it should "prove -> converse" in { check(converseImply) }
  it should "prove domain commute" in { check(domainCommute) }
  it should "prove -> expand" in { check(implyExpand) }
  it should "prove Kd diamond modus ponens" in { check(Kd) }
  it should "prove Kd2 diamond modus ponens" in { check(Kd2) }
  it should "prove PC1" in { check(PC1) }
  it should "prove PC2" in { check(PC2) }
  it should "prove PC3" in { check(PC3) }
  it should "prove -> tautology" in { check { implyTautology } }
  // @todo it should "prove -' neg" in {check(Dneg)}
  // @todo it should "prove -' minus" in {check(Dminus)}
  it should "prove <='" in { check(Dlessequal) }
  it should "prove <'" in { check(Dless) }
  it should "prove ='" in { check(Dequal) }
  it should "prove !='" in { check(Dnotequal) }
  it should "prove ->'" in { check(Dimply) }
  it should "prove \\forall->\\exists" in { check(forallThenExists) }
  // it should "prove DI differential invariance from DI" in {check(DIinvariance)}
  it should "prove DI differential invariant from DI" in { check(DI) }
  it should "prove DIo open differential invariance <" in withMathematica(
    initLibrary = false,
    testcode = { _ => check(DIoless) },
  )
//  it should "prove DV differential variant <=" in withMathematica {_ => check(DVLessEqual)}
  it should "prove DW differential weakening" in { check(DW) }
  it should "prove DW differential weakening and" in { check(DWeakenAnd) }
  it should "prove DR differential refine" in { check(DR) }
  it should "prove DC differential cut" in { check(DC) }
  it should "prove DS no domain" in { check(DSnodomain) }
  it should "prove Dsol& differential equation solution" in { check(DSddomain) }
  it should "prove DGd differential ghost" in { check(DGd) }
  it should "prove DGCd diamond differential ghost const" in { check(DGCd) }
  it should "prove DGCd diamond differential ghost const exists" in { check(DGCde) }
  it should "prove DCd diamond differential cut" in { check(DCdaxiom) }
  it should "prove DWd diamond differential weakening" in { check(DWd) }
  it should "prove DWd2 diamond differential weakening" in { check(DWd2) }
  it should "prove comma commute diamond" in { check(commaCommuted) }
  it should "prove comma commute diamond 2" in { check(commaCommuteD) }
  it should "prove DGd diamond inverse differential ghost implicational" in { check(DGdi) }
  //  it should "prove x' derive var" in {check(Dvar)}
  it should "prove x' derive variable" in { check(DvariableAxiom) }
  it should "prove x' derive var commuted" in withMathematica(
    initLibrary = false,
    testcode = { _ => check(DvariableCommutedAxiom) },
  )
  it should "prove 'linear" in withMathematica(initLibrary = false, testcode = { _ => check(Dlinear) })
  it should "prove 'linear right" in withMathematica(initLibrary = false, testcode = { _ => check(DlinearRight) })
  it should "prove Uniq uniqueness iff" in { check(UniqIff) }
  it should "prove DG differential pre-ghost" in { check(DGpreghost) }
  it should "prove DX diamond differential skip" in { check(dDX) }
  it should "prove DBX>" in withMathematica(initLibrary = false, testcode = { _ => check(DBXgt) })
  it should "prove DBX> open" in withMathematica(initLibrary = false, testcode = { _ => check(DBXgtOpen) })
  it should "prove 0*" in withMathematica(initLibrary = false, testcode = { _ => check(zeroTimes) })
  it should "prove 0+" in withMathematica(initLibrary = false, testcode = { _ => check(zeroPlus) })
  it should "prove +0" in withMathematica(initLibrary = false, testcode = { _ => check(plusZero) })
  it should "prove *0" in withMathematica(initLibrary = false, testcode = { _ => check(timesZero) })
  it should "prove = reflexive" in withMathematica(initLibrary = false, testcode = { _ => check(equalReflexive) })
  it should "prove = commute" in withMathematica(initLibrary = false, testcode = { _ => check(equalCommute) })
  it should "prove <=" in withMathematica(initLibrary = false, testcode = { _ => check(lessEqual) })
  it should "prove ! !=" in withMathematica(initLibrary = false, testcode = { _ => check(notNotEqual) })
  it should "prove >= flip" in withMathematica(initLibrary = false, testcode = { _ => check(flipGreaterEqual) })
  it should "prove > flip" in withMathematica(initLibrary = false, testcode = { _ => check(flipGreater) })
  it should "prove <= flip" in withMathematica(initLibrary = false, testcode = { _ => check(flipLessEqual) })
  it should "prove < flip" in withMathematica(initLibrary = false, testcode = { _ => check(flipLess) })
  it should "prove + associative" in withMathematica(initLibrary = false, testcode = { _ => check(plusAssociative) })
  it should "prove * associative" in withMathematica(initLibrary = false, testcode = { _ => check(timesAssociative) })
  it should "prove + commute" in withMathematica(initLibrary = false, testcode = { _ => check(plusCommute) })
  it should "prove * commute" in withMathematica(initLibrary = false, testcode = { _ => check(timesCommute) })
  it should "prove distributive" in withMathematica(initLibrary = false, testcode = { _ => check(distributive) })
  it should "prove + identity" in withMathematica(initLibrary = false, testcode = { _ => check(zeroPlus) })
  it should "prove * identity" in withMathematica(initLibrary = false, testcode = { _ => check(timesIdentity) })
  it should "prove + inverse" in withMathematica(initLibrary = false, testcode = { _ => check(plusInverse) })
  it should "prove * inverse" in withMathematica(initLibrary = false, testcode = { _ => check(timesInverse) })
  it should "prove positivity" in withMathematica(initLibrary = false, testcode = { _ => check(positivity) })
  it should "prove + closed" in withMathematica(initLibrary = false, testcode = { _ => check(plusClosed) })
  it should "prove * closed" in withMathematica(initLibrary = false, testcode = { _ => check(timesClosed) })
  it should "prove <" in withMathematica(initLibrary = false, testcode = { _ => check(less) })
  it should "prove ! <" in withMathematica(initLibrary = false, testcode = { _ => check(notLess) })
  it should "prove ! <=" in withMathematica(initLibrary = false, testcode = { _ => check(notLessEqual) })
  it should "prove >" in withMathematica(initLibrary = false, testcode = { _ => check(greater) })
  it should "prove ! >" in withMathematica(initLibrary = false, testcode = { _ => check(notGreater) })
  it should "prove ! >=" in withMathematica(initLibrary = false, testcode = { _ => check(notGreaterEqual) })

//  it should "prove != elimination" in withMathematica { _ => check(notEqualElim)}
//  it should "prove >= elimination" in withMathematica { _ => check(greaterEqualElim)}
//  it should "prove > elimination" in withMathematica { _ => check(greaterElim)}
  it should "prove 1>0" in withMathematica(initLibrary = false, testcode = { _ => check(oneGreaterZero) })
  it should "prove nonnegative squares" in withMathematica(
    initLibrary = false,
    testcode = { _ => check(nonnegativeSquares) },
  )
  it should "prove >2!=" in withMathematica(initLibrary = false, testcode = { _ => check(greaterImpliesNotEqual) })
  it should "prove > monotone" in withMathematica(initLibrary = false, testcode = { _ => check(greaterMonotone) })

  it should "prove abs" in withMathematica(
    initLibrary = false,
    testcode = { _ => withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) { check(abs) } },
  )
  it should "prove min" in withMathematica(
    initLibrary = false,
    testcode = { _ => withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) { check(min) } },
  )
  it should "prove max" in withMathematica(
    initLibrary = false,
    testcode = { _ => withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) { check(max) } },
  )
  it should "prove & recusor" in withMathematica(initLibrary = false, testcode = { _ => check(andRecursor) })
  it should "prove | recursor" in withMathematica(initLibrary = false, testcode = { _ => check(orRecursor) })
  it should "prove <= both" in withMathematica(initLibrary = false, testcode = { _ => check(intervalLEBoth) })
  it should "prove < both" in withMathematica(initLibrary = false, testcode = { _ => check(intervalLBoth) })
  it should "prove neg<= up" in withMathematica(initLibrary = false, testcode = { _ => check(intervalUpNeg) })
  it should "prove abs<= up" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) { check(intervalUpAbs) }
    },
  )
  it should "prove max<= up" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) { check(intervalUpMax) }
    },
  )
  it should "prove min<= up" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) { check(intervalUpMin) }
    },
  )
  it should "prove +<= up" in withMathematica(initLibrary = false, testcode = { _ => check(intervalUpPlus) })
  it should "prove -<= up" in withMathematica(initLibrary = false, testcode = { _ => check(intervalUpMinus) })
  it should "prove *<= up" in withMathematica(initLibrary = false, testcode = { _ => check(intervalUpTimes) })
  it should "prove pow<= up" in withMathematica(initLibrary = false, testcode = { _ => check(intervalUpPower) })
  it should "prove 1Div<= up" in withMathematica(initLibrary = false, testcode = { _ => check(intervalUp1Divide) })
  it should "prove <=+ down" in withMathematica(initLibrary = false, testcode = { _ => check(intervalDownPlus) })
  it should "prove <=- down" in withMathematica(initLibrary = false, testcode = { _ => check(intervalDownMinus) })
  it should "prove <=* down" in withMathematica(initLibrary = false, testcode = { _ => check(intervalDownTimes) })
  it should "prove <=pow down" in withMathematica(initLibrary = false, testcode = { _ => check(intervalDownPower) })
  it should "prove <=1Div down" in withMathematica(initLibrary = false, testcode = { _ => check(intervalDown1Divide) })
  it should "prove K& down" in withMathematica(initLibrary = false, testcode = { _ => check(Kand) })
  it should "prove &-> down" in withMathematica(initLibrary = false, testcode = { _ => check(andImplies) })
  it should "prove <= & <=" in withMathematica(initLibrary = false, testcode = { _ => check(metricAndLe) })
  it should "prove < & <" in withMathematica(initLibrary = false, testcode = { _ => check(metricAndLt) })
  it should "prove <= | <=" in withMathematica(initLibrary = false, testcode = { _ => check(metricOrLe) })
  it should "prove < | <" in withMathematica(initLibrary = false, testcode = { _ => check(metricOrLt) })

  it should "prove const congruence" in withMathematica(initLibrary = false, testcode = { _ => check(constCongruence) })
  it should "prove const formula congruence" in withMathematica(
    initLibrary = false,
    testcode = { _ => check(constFormulaCongruence) },
  )

  "Derived Axiom Tactics" should "tactically prove <-> reflexive" in { check(equivReflexive) }
  it should "tactically prove !!" in { check(doubleNegation) }
  it should "tactically prove exists dual" in { check(existsDual) }
  it should "tactically prove all eliminate" taggedAs OptimisticTest ignore { check(alle) }
  it should "tactically prove exists eliminate" in { check(existse) }
  it should "tactically prove all distribute" in { check(allDist) }
  it should "tactically prove exists distribute eliminate" in { check(existsDistElim) }
  it should "tactically prove box dual" in { check(box) }
  it should "tactically prove <:=> assign" in { check(assigndAxiom) }
  it should "tactically prove [:=] equational" in withMathematica(
    initLibrary = false,
    testcode = { _ => check(assignbequational) },
  )
//  it should "tactically prove [:=] equational exists" in {check(assignbExistsAxiom, assignbEquationalT)}
  it should "tactically prove [:=] vacuous assign" in { check(vacuousAssignb) }
  it should "tactically prove <:=> vacuous assign" in { check(vacuousAssignd) }
  it should "tactically prove <':=> differential assign" in { check(Dassignd) }
  it should "tactically prove <++> choice" in { check(choiced) }
  it should "tactically prove <;> compose" in { check(composed) }
  it should "tactically prove <*> iterate" in { check(iterated) }
  it should "tactically prove exists generalize" in { check(existsGeneralize) }
  it should "tactically prove = reflexive" in withMathematica(
    initLibrary = false,
    testcode = { _ => check(equalReflexive) },
  )
  it should "tactically prove = commute" in withMathematica(
    initLibrary = false,
    testcode = { _ => check(equalCommute) },
  )
  it should "tactically prove <=" in withMathematica(initLibrary = false, testcode = { _ => check(lessEqual) })
  it should "tactically prove ! !=" in withMathematica(initLibrary = false, testcode = { _ => check(notNotEqual) })
  it should "tactically prove ! >=" in withMathematica(initLibrary = false, testcode = { _ => check(notGreaterEqual) })
  it should "tactically prove >= flip" in withMathematica(
    initLibrary = false,
    testcode = { _ => check(flipGreaterEqual) },
  )
  it should "tactically prove > flip" in withMathematica(initLibrary = false, testcode = { _ => check(flipGreater) })
  it should "tactically prove all substitute" in { check(allSubstitute) }
  it should "tactically prove vacuous exists" in { check(existsV) }
  it should "tactically prove V[:*] vacuous assign nondet" in { check(vacuousBoxAssignNondet) }
  it should "tactically prove V<:*> vacuous assign nondet" in { check(vacuousDiamondAssignNondet) }
  it should "tactically prove \\forall->\\exists" in { check(forallThenExists) }
  // it should "tactically prove DI differential invariance" in {check(DIinvariance)}
  it should "tactically prove DI differential invariant" in { check(DI) }
  it should "tactically prove DG differential pre-ghost" in { check(DGpreghost) }
  it should "tactically prove DW differential weakening" in { check(DW) }
  it should "tactically prove abs" in withMathematica(
    initLibrary = false,
    testcode = { _ => withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) { check(abs) } },
  )
  it should "tactically prove min" in withMathematica(
    initLibrary = false,
    testcode = { _ => withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) { check(min) } },
  )
  it should "tactically prove max" in withMathematica(
    initLibrary = false,
    testcode = { _ => withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) { check(max) } },
  )

  "Mathematica" should "derive compatibility axiom dgZeroEquilibrium" in withMathematica(
    initLibrary = false,
    testcode = { _ =>
      import TactixLibrary._
      val dgZeroEquilibrium = "x=0 & n>0 -> [{x'=c*x^n}]x=0".asFormula

      TactixLibrary.proveBy(
        dgZeroEquilibrium,
        implyR(1) & dG("y' = ( (-c*x^(n-1)) / 2)*y".asDifferentialProgram, Some("x*y^2=0&y>0".asFormula))(1) &
          TactixLibrary.boxAnd(1, 0 :: Nil) &
          DifferentialTactics.diffInd()(1, 0 :: 0 :: Nil) &
          dG("z' = (c*x^(n-1)/4) * z".asDifferentialProgram, Some("y*z^2 = 1".asFormula))(1, 0 :: 1 :: Nil) &
          dI()(1, 0 :: 1 :: 0 :: Nil) & QE,
      ) shouldBe Symbol("proved")
    },
  )

  "SimplifierV3" should "prove * identity neg" in withMathematica(
    initLibrary = false,
    testcode = { _ => check { timesIdentityNeg } },
  )
  it should "prove -0" in withMathematica(initLibrary = false, testcode = { _ => check { minusZero } })
  it should "prove 0-" in withMathematica(initLibrary = false, testcode = { _ => check { zeroMinus } })
  it should "prove >0 -> !=0" in withMathematica(initLibrary = false, testcode = { _ => check { gtzImpNez } })
  it should "prove <0 -> !=0" in withMathematica(initLibrary = false, testcode = { _ => check { ltzImpNez } })
  it should "prove !=0 -> 0/F" in withMathematica(initLibrary = false, testcode = { _ => check { zeroDivNez } })
  it should "prove F^0" in withMathematica(initLibrary = false, testcode = { _ => check { powZero } })
  it should "prove F^1" in withMathematica(initLibrary = false, testcode = { _ => check { powOne } })

  it should "prove < irrefl" in withMathematica(initLibrary = false, testcode = { _ => check { lessNotRefl } })
  it should "prove > irrefl" in withMathematica(initLibrary = false, testcode = { _ => check { greaterNotRefl } })
  it should "prove != irrefl" in withMathematica(initLibrary = false, testcode = { _ => check { notEqualNotRefl } })
  it should "prove = refl" in withMathematica(initLibrary = false, testcode = { _ => check { equalRefl } })
  it should "prove <= refl" in withMathematica(initLibrary = false, testcode = { _ => check { lessEqualRefl } })
  it should "prove >= refl" in withMathematica(initLibrary = false, testcode = { _ => check { greaterEqualRefl } })

  it should "prove = sym" in withMathematica(initLibrary = false, testcode = { _ => check { equalSym } })
  it should "prove != sym" in withMathematica(initLibrary = false, testcode = { _ => check { equalSym } })
  it should "prove > antisym" in withMathematica(initLibrary = false, testcode = { _ => check { greaterNotSym } })
  it should "prove < antisym" in withMathematica(initLibrary = false, testcode = { _ => check { lessNotSym } })

  // @note must be last to populate the lemma database during build
  "The DerivedAxioms prepopulation procedure" should "not crash" ignore withMathematica(
    initLibrary = false,
    testcode = { _ =>
      LemmaDBFactory.lemmaDB.deleteDatabase()
      withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
        val writeEffect = true
        // use a new instance of the DerivedAxioms singleton object to store all axioms to the lemma database
        val c = Ax.getClass.getDeclaredConstructor()
        c.setAccessible(true)
        c.newInstance().asInstanceOf[Ax.type].prepopulateDerivedLemmaDatabase()

        val cache = new File(Configuration.path(Configuration.Keys.LEMMA_CACHE_PATH))
        // see [[FileLemmaDB.scala]] for path of actual lemma files
        val lemmaFiles = new File(cache.getAbsolutePath + File.separator + "lemmadb")
          .listFiles(new FilenameFilter() {
            override def accept(dir: File, name: String): Boolean = name.endsWith(".alp")
          })
          .map(_.getName.stripSuffix(".alp"))
        val infos = getDerivedAxiomsMirrors.map({ case (valName, m) => valName -> m().asInstanceOf[StorableInfo] })
        // we allow lazy val forwarding, but all of them have to refer to the same lemma
        val forwards = infos
          .groupBy({ case (_, info) => info })
          .filter((kv: (StorableInfo, Array[(String, StorableInfo)])) => kv._2.length > 1)
        // the lemma database only stores the one lemma referred to from one or more lazy vals
        lemmaFiles.length shouldBe lemmaFiles.distinct.length
        // the lemma database stores all the distinct lemmas in DerivedAxioms
        forwards.keys.map(_.storedName).toList.diff(lemmaFiles) shouldBe empty

        if (writeEffect) {
          val versionFile = new File(cache.getAbsolutePath + File.separator + "VERSION")
          if (!versionFile.exists()) {
            if (!versionFile.createNewFile()) throw new Exception(s"Could not create ${versionFile.getAbsolutePath}")
          }
          assert(versionFile.exists())
          val fw = new FileWriter(versionFile)
          fw.write(edu.cmu.cs.ls.keymaerax.core.VERSION)
          fw.close()
        }
      }
    },
  )

  /** Returns the reflection mirrors to access the lazy vals in DerivedAxioms. */
  private def getDerivedAxiomsMirrors = {
    val lemmas = Ax.getClass.getDeclaredFields.filter(f => classOf[StorableInfo].isAssignableFrom(f.getType))
    val fns = lemmas.map(_.getName)

    val mirror = ru.runtimeMirror(getClass.getClassLoader)
    // access the singleton object
    val moduleMirror = mirror.reflectModule(ru.typeOf[Ax.type].termSymbol.asModule)
    val im = mirror.reflect(moduleMirror.instance)

    // @note lazy vals have a "hidden" getter method that does the initialization
    val fields = fns.map(fn => fn -> ru.typeOf[Ax.type].member(ru.TermName(fn)).asMethod.getter.asMethod)
    fields.map(f => f._2.toString -> im.reflectMethod(f._2))
  }
}
