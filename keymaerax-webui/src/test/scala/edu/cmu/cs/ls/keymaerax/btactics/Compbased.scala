/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.ModelPlex.createMonitorSpecificationConjecture
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.language.postfixOps
import org.scalatest.LoneElement._

import scala.collection.immutable.List

/**
  * Component-based proving test cases (FASE).
  * @author Stefan Mitsch
  */
@SlowTest
class Compbased extends TacticTestBase {

  private val namespace = "components"

  /** STTT Lemma 1 Corollaries */
  private lazy val assignmentIndependence1 = AnonymousLemmas.remember(
    "[x_:=s_();][y_:=t_();]p_(x_,y_) <-> [y_:=t_();][x_:=s_();]p_(x_,y_)".asFormula,
    master() & done,
    namespace
  )
  private lazy val assignmentIndependence2 = AnonymousLemmas.remember(
    "[x_:=*;][y_:=t_();]p_(x_,y_) <-> [y_:=t_();][x_:=*;]p_(x_,y_)".asFormula,
    master() & allL('Llast) & closeId & done,
    namespace
  )
  private lazy val assignmentIndependence3 = AnonymousLemmas.remember(
    "[x_:=*;][y_:=*;]p_(x_,y_) <-> [y_:=*;][x_:=*;]p_(x_,y_)".asFormula,
    master() & done,
    namespace
  )
  private lazy val assignmentIndependence4 = AnonymousLemmas.remember(
    "[x_:=s_();][?q_();]p_(x_) <-> [?q_();][x_:=s_();]p_(x_)".asFormula,
    master() & done,
    namespace
  )
  private lazy val assignmentIndependence5 = AnonymousLemmas.remember(
    "[x_:=*;][?q_();]p_(x_) <-> [?q_();][x_:=*;]p_(x_)".asFormula,
    chase(1, 0::Nil) & chase(1, 1::Nil) & equivR(1) <(
      implyR(1) & allR(1) & allL(-1) & prop & done,
      allR(1) & implyR(1) & implyL(-1) <(closeId, allL(-1) & closeId) & done
    ) & done,
    namespace
  )
  private lazy val testIndependence = AnonymousLemmas.remember(
    "[?q_();][?r_();]p_() <-> [?r_();][?q_();]p_()".asFormula,
    master() & done,
    namespace
  )

  /** STTT Lemma 1 */
  private lazy val programIndependence: DependentPositionTactic = "programIndependence" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(Assign(x, s), Box(Assign(y, t), p))) =>
        val rensubst = (_: Option[Subst]) => RenUSubst(
          "x_".asVariable -> x ::
          "y_".asVariable -> y ::
          "s_()".asTerm -> s ::
          "t_()".asTerm -> t ::
          PredOf(Function("p_", None, Tuple(Real, Real), Bool), "(._1,._2)".asTerm) -> p.replaceFree(x, "._1".asTerm).replaceFree(y, "._2".asTerm) :: Nil
        )
        useAt(assignmentIndependence1, PosInExpr(0::Nil), rensubst)(pos)
      case Some(Box(Assign(x, s), Box(AssignAny(y), p))) =>
        val rensubst = (_: Option[Subst]) => RenUSubst(
          "x_".asVariable -> y ::
          "y_".asVariable -> x ::
          "t_()".asTerm -> s ::
          PredOf(Function("p_", None, Tuple(Real, Real), Bool), "(._1,._2)".asTerm) -> p.replaceFree(x, "._2".asTerm).replaceFree(y, "._1".asTerm) :: Nil
        )
        useAt(assignmentIndependence2, PosInExpr(1::Nil), rensubst)(pos)
      case Some(Box(_: Assign, Box(_: Test, _))) => useAt(assignmentIndependence4)(pos)
      case Some(Box(AssignAny(x), Box(Assign(y, t), p))) =>
        val rensubst = (_: Option[Subst]) => RenUSubst(
          "x_".asVariable -> x ::
          "y_".asVariable -> y ::
          "t_()".asTerm -> t ::
          PredOf(Function("p_", None, Tuple(Real, Real), Bool), "(._1,._2)".asTerm) -> p.replaceFree(x, "._1".asTerm).replaceFree(y, "._2".asTerm) :: Nil
        )
        useAt(assignmentIndependence2, PosInExpr(0::Nil), rensubst)(pos)
      case Some(Box(AssignAny(x), Box(AssignAny(y), p))) =>
        val rensubst = (_: Option[Subst]) => RenUSubst(
          "x_".asVariable -> x ::
          "y_".asVariable -> y ::
          PredOf(Function("p_", None, Tuple(Real, Real), Bool), "(._1,._2)".asTerm) -> p.replaceFree(x, "._1".asTerm).replaceFree(y, "._2".asTerm) :: Nil
        )
        useAt(assignmentIndependence3, PosInExpr(0::Nil), rensubst)(pos)
      case Some(Box(_: AssignAny, Box(_: Test, _))) => useAt(assignmentIndependence5)(pos)
      case Some(Box(_: Test, Box(_: Test, _))) => useAt(testIndependence)(pos)
      case Some(Box(_: Test, Box(_: Assign, _))) => useAt(assignmentIndependence4, PosInExpr(1::Nil))(pos)
      case Some(Box(Compose(a,b), p)) =>
        composeb(pos) & programIndependence(pos) & useAt("[;] compose", PosInExpr(1::Nil))(pos)
      case Some(have@Box(a, Box(b, p))) =>
        val swapped = proveBy(Equiv(Box(b, Box(a, p)), have), chase(1, 0::Nil) & chase(1, 1::Nil) & QE)
        useAt(swapped, PosInExpr(1::Nil))(pos)
    }
  })

  /** STTT Lemma 2 */
  private lazy val dropControl = "dropControl" by ((pos: Position, seq: Sequent) => {
    require(pos.isSucc, "Drop control only in succedent")
    val lemma2 = seq.sub(pos) match {
      case Some(have@Box(a, Box(b, p))) if
        StaticSemantics.freeVars(p).intersect(StaticSemantics.boundVars(b)).isEmpty &&
        StaticSemantics.freeVars(a).intersect(StaticSemantics.boundVars(b)).isEmpty =>
          proveBy(Imply(Box(a, p), have), implyR(1) & monb & abstractionb(1) & closeId & done)
      case Some(have@Box(b, Box(a, p))) if
        StaticSemantics.freeVars(p).intersect(StaticSemantics.boundVars(b)).isEmpty &&
        StaticSemantics.freeVars(a).intersect(StaticSemantics.boundVars(b)).isEmpty =>
          proveBy(Imply(Box(a, p), have), implyR(1) & abstractionb(1) & closeId & done)
      case Some(have@Box(a, p)) if
        p.isFOL &&
        StaticSemantics.freeVars(p).intersect(StaticSemantics.boundVars(a)).isEmpty &&
        StaticSemantics.freeVars(a).intersect(StaticSemantics.boundVars(a)).isEmpty =>
        proveBy(Imply(p, have), implyR(1) & abstractionb(1) & closeId & done)
    }
    useAt(lemma2, PosInExpr(1::Nil))(pos)
  })

  /** STTT Lemma 3 */
  private def dropPlant(keep: Set[Variable]) = "dropPlant" by ((pos: Position, seq: Sequent) => {
    require(pos.isSucc, "Drop plant only in succedent")
    val lemma3 = seq.sub(pos) match {
      case Some(have@Box(ODESystem(ode, hq), p)) =>
        val (xs, ys) = DifferentialHelper.atomicOdes(ode).partition(o => keep.contains(o.xp.x))
        val (hs, qs) = FormulaTools.conjuncts(hq).partition(StaticSemantics.freeVars(_).intersect(ys.map(_.xp.x).toSet).isEmpty)
        val h = hs.reduceOption(And).getOrElse(True)
        val q = qs.reduceOption(And).getOrElse(True)
        require(StaticSemantics.freeVars(p).intersect(ys.map(_.xp.x).toSet).isEmpty, "Postcondition p must be independent of ys")
        require(xs.flatMap(x => StaticSemantics.freeVars(x.e).toSet).intersect(ys.map(_.xp.x)).isEmpty, "Right-handside of x'=theta must not overlap primed ys")
        require(ys.flatMap(y => StaticSemantics.freeVars(y.e).toSet).intersect(xs.map(_.xp.x)).isEmpty, "Right-handside of y'=eta must not overlap primed ys")

        xs.reduceOption(DifferentialProduct.apply) match {
          case Some(xsys) =>
            ys.reduceOption(DifferentialProduct.apply) match {
              case Some(ysys) =>
                val universalXClosure = ys.map(_.xp.x).foldLeft[Formula](Box(ODESystem(ode, h), p))((f, y) => Forall(y::Nil, f))
                val partitionedOdeLemma =
                  proveBy(Imply(Box(ODESystem(DifferentialProduct(ysys, xsys), h), p), Box(ODESystem(ode, h), p)),
                    implyR(1) &
                    //sort ys into reverse order because we apply DGi outside in (innermost universal quantifier first)
                    AxiomaticODESolver.selectionSort(h, p, ode, ys.map(_.xp.x)++xs.map(_.xp.x), SuccPosition(1)) &
                    closeId)
                proveBy(Imply(Box(ODESystem(xsys, h), p), have),
                  implyR(1) & DifferentialTactics.diffRefine(h)(1) <(
                    cut(universalXClosure) <(
                      allL('Llast)*ys.size & closeId & done
                      ,
                      hideR(1) & useAt(partitionedOdeLemma, PosInExpr(1::Nil))(1, List.fill(ys.size)(0)) &
                      ys.indices.reverse.
                        map(i => PosInExpr(List.fill(i)(0))).
                        map(useAt("DG inverse differential ghost implicational", PosInExpr(1::Nil))(1, _)).
                        reduceOption[BelleExpr](_ & _).getOrElse(skip) &
                      closeId & done
                    ),
                    cohideR(1) & dW(1) & prop & done
                  )
                )
              case None => proveBy(Equiv(have, have), byUS(DerivedAxioms.equivReflexiveAxiom))
            }
          case None => ??? //@todo
        }
    }
    useAt(lemma3, PosInExpr(1::Nil))(pos)
  })

  /** STTT Lemma 4 */
  private def overapproximateProgram = "overapproximateProgram" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(have@Box(a, p)) =>
        val abv = StaticSemantics.boundVars(a).intersect(StaticSemantics.freeVars(p)).toSet.toList
        val approximate = abv.indices.reverse.
          map(i => PosInExpr(List.fill(i)(0))).
          map(useAt("[:*] assign nondet", PosInExpr(1::Nil))(1, _)).reduceOption[BelleExpr](_ & _).getOrElse(skip)
        val decompose = Range(0, abv.size-1).
          map(i => PosInExpr(List.fill(i)(1))).
          map(useAt("[;] compose")(-1, _)).reduceOption[BelleExpr](_ & _).getOrElse(skip)
        val lemma4 = proveBy(
          Imply(Box(abv.map(AssignAny).reduceRightOption(Compose).getOrElse(Test(True)), p), have),
          implyR(1) & abstractionb(1) & approximate & decompose & closeId)
        useAt(lemma4, PosInExpr(1::Nil))(pos)
    }
  })

  /** STTT Lemma 5 */
  private lazy val introduceTestLemma = AnonymousLemmas.remember(
    "[a{|^@|};]q(||) -> ([a{|^@|};][?q(||);]p(||) <-> [a{|^@|};]p(||))".asFormula,
    implyR(1) & equivR(1) <(
      testb(-2, 1::Nil),
      testb(1, 1::Nil)
    ) & onAll(implyRi()(-2, 1) & useAt("K modal modus ponens", PosInExpr(1::Nil))(1) & monb & prop & done), namespace)

  private def introduceTest(f: Formula) = "introduceTest" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(a, p)) =>
        val subst = (_: Option[Subst]) => RenUSubst(
          SystemConst("a") -> a ::
          "p(||)".asFormula -> p ::
          "q(||)".asFormula -> f :: Nil
        )
        useAt(introduceTestLemma, PosInExpr(1::1::Nil), subst)(pos)
    }
  })

  /** STTT Lemma 6 */
  private lazy val weakenTestLemma = AnonymousLemmas.remember(
    "(r_() -> q_()) -> [?q_();]p_() -> [?r_();]p_()".asFormula,
    testb(1, 1::0::Nil) & testb(1, 1::1::Nil) & prop & done,
    namespace)

  private lazy val diamondToBox = AnonymousLemmas.remember(
    "<a;>true -> ([a;]p_(||) -> <a;>p_(||))".asFormula,
    implyR(1) & implyR(1) /* todo */ & done
  )

  private def weakenTest(f: Formula) = "weakenTest" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(Test(r), p)) =>
        val subst = (_: Option[Subst]) => RenUSubst(
          "r_()".asFormula -> r ::
          "p_()".asFormula -> p ::
          "q_()".asFormula -> f :: Nil
        )
        useAt(weakenTestLemma, PosInExpr(1::1::Nil), subst)(pos)
    }
  })

  /** STTT Fig. 12 */
  private def useCompatibility(compatibility: Lemma, plant1Vars: Set[Variable]) = "useCompatibility" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(delta, Box(ctrl, Box(Assign(told,t), Box(plant, Box(in1star, Box(cons, Imply(pi2out, pi1in)))))))) =>
      useAt(compatibility, PosInExpr(1::Nil))(pos ++ PosInExpr(List.fill(5)(1))) & DebuggingTactics.print("Applied compatibility lemma") &
      dropControl(pos ++ PosInExpr(1::1::1::1::Nil)) &
      dropPlant(plant1Vars)(pos ++ PosInExpr(1::1::1::Nil)) &
      dropControl(pos ++ PosInExpr(1::1::Nil)) &
      dropControl(pos ++ PosInExpr(1::Nil)) &
      dropControl(pos) & DebuggingTactics.print("Dropped all statements except port memory") &
      chase(1) & prop & DebuggingTactics.done("Fig. 12 done")
  })

  private def proveSystemCompStep4(inputAssumptions: Map[Set[Variable],Formula], outputGuarantees: Map[Set[Variable],Formula],
                                   plant1Vars: Set[Variable],
                                   compatibility: Lemma, remainingCons: Int): DependentPositionTactic = "proveSystemCompStep4" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(_) if remainingCons <= 0 => skip
    case Some(Box(cons, _)) if remainingCons > 0 =>

      val headConVar = cons match {
        case Compose(l, _) => StaticSemantics.boundVars(l).toSet
        case p => StaticSemantics.boundVars(p).toSet
      }

      (if (remainingCons > 1) composeb(pos) else skip) &
      // Step 2.7 (introduce output guarantee of component 2)
      introduceTest(outputGuarantees(headConVar))(pos.topLevel ++ pos.inExpr.parent.parent) <(skip, prop & done) & DebuggingTactics.print("Introduced test") &
      // Step 2.8 (move output guarantee past connection)
      programIndependence(pos.topLevel ++ pos.inExpr.parent) & programIndependence(pos) & DebuggingTactics.print("Moved test") &
      // Step 2.9 (weaken output guarantee to input assumption)
      weakenTest(inputAssumptions(headConVar))(pos ++ PosInExpr(1::Nil)) <(
        skip,
        useCompatibility(compatibility, plant1Vars)(pos.topLevel)
      ) & DebuggingTactics.print("Weakened test") &
      // Step 2.10
      overapproximateProgram(pos) & DebuggingTactics.print("Overapproximated program") &
      // Step 2.11
      useAt("[;] compose", PosInExpr(1::Nil))(pos) & useAt("[;] compose", PosInExpr(1::Nil))(pos.topLevel ++ pos.inExpr.parent) &
      // recurse until done
      proveSystemCompStep4(inputAssumptions, outputGuarantees, plant1Vars, compatibility, remainingCons-1)(pos)
  })

  private def leftAssignments(program: Program, length: Int = -1): List[Program] = {
    def leftAssignments(program: Program, length: Int, count: Int): List[Program] = program match {
      case Compose(p, q) if length == -1 || count < length => leftAssignments(p, length, count+1) :+ q
      case f => List(f)
    }
    leftAssignments(program, length, 1) //@note not splitting is a list of length 1
  }

  private def atoms(program: Program): List[Program] = program match {
    case Compose(l, r) => atoms(l) ++ atoms(r)
    case _ => program :: Nil
  }

  private def ports(program: Program): List[(Program, Test)] = {
    def ports(programs: List[Program]): List[(Program, Test)] = {
      if (programs.isEmpty) Nil
      else {
        val (p1, tail) = programs.span({ case _: Test => false case _ => true })
        (p1.reduce(Compose) -> tail.head.asInstanceOf[Test]) +: ports(tail.tail)
      }
    }
    ports(atoms(program))
  }

  /** STTT Fig. 13 */
  private def justifyFout(fout: Formula, keepPlantVars: Set[Variable], comGuaranteeLiveness: Lemma) = "justifyFout" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(_: Imply) =>
      val Diamond(a, _) = comGuaranteeLiveness.fact.conclusion.succ.head
      val Imply(_ , Box(_, Box(_, Box(_, Box(_, foutSafety))))) = fout

      cohideR(pos) & dropPlant(keepPlantVars)(1, 1::1::1::1::Nil) & DebuggingTactics.print("Dropped plant1") &
      composeb(1, 1::1::Nil) & dropControl(1, 1::1::Nil) & DebuggingTactics.print("Dropped ctrl1") &
      composeb(1, 1::Nil) & dropControl(1, 1::Nil) & DebuggingTactics.print("Dropped delta1") &
      cutAt(Diamond(a, foutSafety))(1, 1::1::1::1::1::Nil) & DebuggingTactics.print("Now what?") <(
        // use
        /*useAt(diamondToBox, PosInExpr(1::Nil))(1, 1::1::1::1::1::Nil) &*/ DebuggingTactics.print("Foo")
        ,
        // show
        CMon(1, 1::1::1::1::1::1::Nil) & implyR(1) & useAt("<> diamond", PosInExpr(1::Nil))(-1) & notL(-1) & abstractionb(2) & prop & done
      )
  })

  /** STTT Fig. 11 */
  private def proveSystemCompStep(step: Lemma, compatibility: Lemma, comGuaranteeLiveness: Lemma, fout: Formula) = "proveSystemCompStep" by ((pos: Position, seq: Sequent) => {
    require(pos.isTopLevel)
    seq.sub(pos) match {
      case Some(Box(delta3, Box(Compose(ctrl1,ctrl2), Box(rememberStart@Assign(told, t), Box(ODESystem(DifferentialProduct(time, plant3), q3), Box(Compose(in3,cp3), inv1)))))) =>
        val Box(Compose(delta1, Compose(_/*ctrl1*/, Compose(_/*rememberStart*/, Compose(plant1, Compose(in1, cp1))))), _) = step.fact.conclusion.succ.head

        val piouts = fout match {
          case Imply(_, Box(delta, Box(ctrl, Box(remember, Box(plant, pi2Out))))) => FormulaTools.leftConjuncts(pi2Out)
        }
        //val c2outvars = piouts.flatMap(StaticSemantics.freeVars(_).toSet).toSet

        val plant1Vars = StaticSemantics.boundVars(plant1).toSet.filter(_.isInstanceOf[BaseVariable])
        val plant2Vars = (StaticSemantics.boundVars(plant3).toSet.filter(_.isInstanceOf[BaseVariable]) -- plant1Vars) ++
          StaticSemantics.boundVars(time).toSet.filter(_.isInstanceOf[BaseVariable])

        val Compose(_, Compose(_, con)) = cp3
        val connections = leftAssignments(con, piouts.size)
        val foo = connections.map(p => StaticSemantics.boundVars(p) -> StaticSemantics.freeVars(p)).toMap
        val connectedVars = connections.flatMap(StaticSemantics.boundVars(_).toSet).toSet
        //val connectionsFromC2 = connections.filter(c => !StaticSemantics.freeVars(c).intersect(c2outvars).isEmpty)

        val in1cons = ports(in1).filter({ case (port, pin) => !StaticSemantics.boundVars(port).intersect(connectedVars).isEmpty })
        val in1Assumptions = in1cons.map({ case (port, pin) => StaticSemantics.boundVars(port).toSet -> pin.cond }).toMap
        val guarantees = in1cons.map({ case (port, _) =>
          StaticSemantics.boundVars(port).toSet ->
          piouts.find(piout => !foo(StaticSemantics.boundVars(port)).intersect(StaticSemantics.freeVars(piout)).isEmpty).getOrElse(True) }).toMap

        cut(fout) <(
          // use
          //@todo S2.2 reorder to in1^*;in2^* (for now: assume they are in the right order)
          (4 to 6).map(i => PosInExpr(List.fill(i)(1))).map(i => composeb(pos ++ i)).reduce[BelleExpr](_&_) &
          composeb(pos ++ PosInExpr(List.fill(4)(1))) & // decompose in3 into [in1*][in2*]
          // Step 2.3 (move con between in1* and in2*)
          (5 to 7).map(i => PosInExpr(List.fill(i)(1))).reverse.map(programIndependence(1, _)).reduce[BelleExpr](_&_) &
            DebuggingTactics.print("Step 2.3 done") &
          // Step 2.4 (drop cp2)
          dropControl(pos ++ PosInExpr(List.fill(8)(1))) & DebuggingTactics.print("Step 2.4 done") &
          // Step 2.5 (drop in2*)
          dropControl(pos ++ PosInExpr(List.fill(6)(1))) & DebuggingTactics.print("Step 2.5 done") &
          // Steps 2.6-2.11, note that reserved time `t` is present in contract models but not part of the plant per STTT
          proveSystemCompStep4(in1Assumptions, guarantees, plant1Vars.filter(_.name != "t"), compatibility, in1Assumptions.size)(pos ++ PosInExpr(List.fill(5)(1))) &
          DebuggingTactics.print("Steps 2.6-2.11 done") &
          dropPlant(plant1Vars)(pos ++ PosInExpr(1::1::1::Nil)) & DebuggingTactics.print("Step 2.12 done") &
          composeb(pos ++ PosInExpr(1::Nil)) & dropControl(pos ++ PosInExpr(1::1::Nil)) & // drop ctrl2
          composeb(pos) & dropControl(pos ++ PosInExpr(1::Nil)) & DebuggingTactics.print("Step 2.13 done") & // drop delta2
          hideL('Llast) &
          // use step lemma
          ("ANON" by ((pp: Position, ss: Sequent) => ss.sub(pp) match {
            case Some(have@Box(_, p)) =>
              useAt(proveBy(Equiv(Box(in1, p), have), chase(1, 0::Nil) & chase(1, 1::Nil) & QE), PosInExpr(1::Nil))(pp)
          }))(pos ++ PosInExpr(1::1::1::1::Nil)) & DebuggingTactics.print("Using step lemma") &
          useLemma(step, Some((0 to 4).map(i => PosInExpr(1 +: List.fill(i)(1))).map(i => composeb(LastAnte(0, i))).reduce[BelleExpr](_&_) & prop)) &
          DebuggingTactics.print("Step done") & DebuggingTactics.done("Step")
          ,
          // show
          justifyFout(fout, plant2Vars, comGuaranteeLiveness)('Rlast)
        )
    }
  })

  /** STTT Fig. 10 */
  private def proveSystemStep(c1step: Lemma, c2step: Lemma, pi1Out: Formula, pi2Out: Formula,
                              compatibility: Lemma, comGuaranteeSafety: Lemma, comGuaranteeLiveness: Lemma) = "proveSystemStep" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(Compose(delta3, Compose(ctrl3, Compose(rememberStart@Assign(told, t), Compose(plant3@ODESystem(DifferentialProduct(_, _), q3), Compose(in3, Compose(cp1, Compose(cp2, con))))))), inv3@And(inv1, And(inv2, zeta)))) =>
      //@todo check program shapes in lemmas
      val cr1 :: cr2 :: Nil = (0 to 3) :: (4 to 6) :: Nil
      boxAnd(1) & andR(1) <(
        // inv1
        cr1.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
          proveSystemCompStep(c1step, compatibility, comGuaranteeLiveness, Imply(inv2, Box(delta3, Box(ctrl3, Box(rememberStart, Box(plant3, pi2Out))))))(pos)
        ,
        boxAnd(1) & andR(1) <(
          // inv2
          cr1.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) /*&
            proveSystemCompStep(c2step, Imply(inv1, Box(delta3, Box(ctrl3, Box(rememberStart, Box(plant3, pi1Out))))))(pos)*/
          ,
          // zeta
          cr1.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
          cr2.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
          (cr1.head to cr2.last).map(i => PosInExpr(List.fill(i)(1))).reverse.map(abstractionb(1, _)).reduce[BelleExpr](_ & _) &
          (allR(1)*) & cohideR(1) & by(comGuaranteeSafety) & DebuggingTactics.done("Zeta Step")
        )
      )

//      cr1.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
//      boxAnd(1, List.fill(cr1.last+1)(1)) & andR(1) <(
//        // inv1
//        skip
//        ,
//        boxAnd(1, List.fill(cr1.last+1)(1)) & andR(1) <(
//          // inv2
//          skip
//          ,
//          // zeta
//          cr2.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) & DebuggingTactics.print("Decomposed") &
//          (cr1.head to cr2.last).map(i => PosInExpr(List.fill(i)(1))).reverse.map(abstractionb(1, _)).reduce[BelleExpr](_ & _) & DebuggingTactics.print("Abstracted") &
//          (allR(1)*) & DebuggingTactics.print("AllR") & by(comGuarantee)
//        )
//      )
  })

  /** STTT Fig. 9 */
  private def proveSystem(c1base: Lemma, c1use: Lemma, c1step: Lemma,
                          c2base: Lemma, c2use: Lemma, c2step: Lemma,
                          compatibility: Lemma, comGuaranteeSafety: Lemma, comGuaranteeLiveness: Lemma) = "proveSystem" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Imply(And(timeInit, And(globalFacts, And(init1, And(init2, zeta)))), Box(Loop(sys), And(post1, post2)))) =>
      //@todo check lemma shapes
      val inv1 = c1base.fact.conclusion.succ.head
      val inv2 = c2base.fact.conclusion.succ.head
      val (safe1, pi1Out) = post1 match {
        case And(l, r) => (l, r)
        case f => (f, f)
      }
      val (safe2, pi2Out) = post2 match {
        case And(l, r) => (l, r)
        case f => (f, f)
      }
      implyR(1) & loop(And(inv1, And(inv2, zeta)))(1) <(
        andR(1) <(
          useLemma(c1base, Some(prop)) & DebuggingTactics.done("C1Base"),
          andR(1) <(
            useLemma(c2base, Some(prop)) & DebuggingTactics.done("C2Base"),
            prop & DebuggingTactics.done("ZetaBase")
          )
        ),
        andR(1) <(
          useLemma(c1use, Some(prop)) & DebuggingTactics.done("C1Use"),
          useLemma(c2use, Some(prop)) & DebuggingTactics.done("C2Use")
        ),
        proveSystemStep(c1step, c2step, pi1Out, pi2Out, compatibility, comGuaranteeSafety, comGuaranteeLiveness)(1)
      )
  })

  private def proveSystem(c1baseLemma: String, c1useLemma: String, c1stepLemma: String,
                          c2baseLemma: String, c2useLemma: String, c2stepLemma: String,
                          compatibilityLemma: String, comGuaranteeSafetyLemma: String, comGuaranteeLivenessLemma: String): DependentPositionTactic = {
    proveSystem(
      LemmaDBFactory.lemmaDB.get("user/" + c1baseLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c1useLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c1stepLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c2baseLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c2useLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c2stepLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + compatibilityLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + comGuaranteeSafetyLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + comGuaranteeLivenessLemma).get
    )
  }

  "Lemma 1" should "work for easy case" in withMathematica { _ =>
    proveBy("[x:=2;][y:=3;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [y:=3;][x:=2;]x+y>=5".asSequent
    proveBy("[x:=2;][y:=*;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [y:=*;][x:=2;]x+y>=5".asSequent
    proveBy("[x:=*;][y:=3;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [y:=3;][x:=*;]x+y>=5".asSequent
    proveBy("[x:=2;][?y>=3;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [?y>=3;][x:=2;]x+y>=5".asSequent
    proveBy("[x:=*;][?y>=3;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [?y>=3;][x:=*;]x+y>=5".asSequent
    proveBy("[?x>=2;][?y>=3;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [?y>=3;][?x>=2;]x+y>=5".asSequent
  }

  it should "work in context" in withMathematica { _ =>
    proveBy("[z:=1;][x:=2;][y:=3;]x+y>=5".asFormula, programIndependence(1, 1::Nil)).subgoals.loneElement shouldBe "==> [z:=1;][y:=3;][x:=2;]x+y>=5".asSequent
    proveBy("[?z>=1;][x:=2;][y:=*;]x+y>=5".asFormula, programIndependence(1, 1::Nil)).subgoals.loneElement shouldBe "==> [?z>=1;][y:=*;][x:=2;]x+y>=5".asSequent
    proveBy("[?z>=0;][?a<=1;][x:=*;][y:=3;]x+y>=5".asFormula, programIndependence(1, 1::1::Nil)).subgoals.loneElement shouldBe "==> [?z>=0;][?a<=1;][y:=3;][x:=*;]x+y>=5".asSequent
    proveBy("[?z>=0;][a:=1;][x:=2;][?y>=3;]x+y>=5".asFormula, programIndependence(1, 1::1::Nil)).subgoals.loneElement shouldBe "==> [?z>=0;][a:=1;][?y>=3;][x:=2;]x+y>=5".asSequent
    proveBy("[?z>=0;][a:=*;][x:=*;][?y>=3;]x+y>=5".asFormula, programIndependence(1, 1::1::Nil)).subgoals.loneElement shouldBe "==> [?z>=0;][a:=*;][?y>=3;][x:=*;]x+y>=5".asSequent
    proveBy("[?x>=2;][?y>=3;]x+y>=5 -> z>=2".asFormula, programIndependence(1, 0::Nil)).subgoals.loneElement shouldBe "==> [?y>=3;][?x>=2;]x+y>=5 -> z>=2".asSequent
  }

  it should "work when boxes are not split" in withMathematica { _ =>
    proveBy("[x:=2;y:=3;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [y:=3;x:=2;]x+y>=5".asSequent
    proveBy("[x:=2;y:=*;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [y:=*;x:=2;]x+y>=5".asSequent
    proveBy("[x:=*;y:=3;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [y:=3;x:=*;]x+y>=5".asSequent
    proveBy("[x:=2;?y>=3;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [?y>=3;x:=2;]x+y>=5".asSequent
    proveBy("[x:=*;?y>=3;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [?y>=3;x:=*;]x+y>=5".asSequent
    proveBy("[?x>=2;?y>=3;]x+y>=5".asFormula, programIndependence(1)).subgoals.loneElement shouldBe "==> [?y>=3;?x>=2;]x+y>=5".asSequent
  }

  "Lemma 2" should "work for easy case" in withMathematica { _ =>
    proveBy("[x:=2;][y:=3;]y>=3".asFormula, dropControl(1)).subgoals.loneElement shouldBe "==> [y:=3;]y>=3".asSequent
    proveBy("[x:=2;][y:=3;]x>=2".asFormula, dropControl(1)).subgoals.loneElement shouldBe "==> [x:=2;]x>=2".asSequent
  }

  "Lemma 3" should "work for easy case" in withMathematica { _ =>
    proveBy("x>=0 ==> [{x'=1,y'=2}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [{x'=1}]x>=0".asSequent
    proveBy("x>=0 ==> [{x'=1,y'=2 & x>=-1 & y<=4}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [{x'=1 & x>=-1}]x>=0".asSequent
    proveBy("x>=0 ==> [{x'=1,y'=2 & y<=4 & x>=-1}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [{x'=1 & x>=-1}]x>=0".asSequent
    proveBy("x>=0 ==> [{x'=1,y'=2,z'=3}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [{x'=1}]x>=0".asSequent
    proveBy("x>=0 ==> [{x'=1}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [{x'=1}]x>=0".asSequent
    //proveBy("x>=0 ==> [{y'=1}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [?true;]x>=0".asSequent
  }

  "Lemma 4" should "work for easy case" in withMathematica { _ =>
    proveBy("[x:=5;]x>=0".asFormula, overapproximateProgram(1)).subgoals.loneElement shouldBe "==> [x:=*;]x>=0".asSequent
    proveBy("[x:=5;y:=6;z:=7;]x>=0".asFormula, overapproximateProgram(1)).subgoals.loneElement shouldBe "==> [x:=*;]x>=0".asSequent
    proveBy("[x:=5;y:=6;z:=7;]x+y+z>=0".asFormula, overapproximateProgram(1)).subgoals.loneElement shouldBe "==> [x:=*;y:=*;z:=*;]x+y+z>=0".asSequent
  }

  "Lemma 5" should "work" in withMathematica { _ =>
    proveBy("[x:=3;]x>=1".asFormula, introduceTest("x>=2".asFormula)(1) <(skip, master())).subgoals.loneElement shouldBe "==> [x:=3;][?x>=2;]x>=1".asSequent
  }

  "Lemma 6" should "work" in withMathematica { _ =>
    proveBy("[?x>=5;]x>=2".asFormula, weakenTest("x>=2".asFormula)(1)).subgoals.loneElement shouldBe "==> [?x>=2;]x>=2".asSequent
  }

  "STTT Examples" should "prove remote control contract compliance" in withMathematica { _ =>
    val entry = KeYmaeraXArchiveParser.getEntry("Remote Control Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._2) shouldBe 'proved)
  }

  it should "prove obstacle contract compliance" in withMathematica { _ =>
    val entry = KeYmaeraXArchiveParser.getEntry("Obstacle Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._2) shouldBe 'proved)
  }

  it should "prove choice implementation" in withMathematica { _ =>
    val s = Variable("s")
    def implementChoice(a: Program, b: Program, p: Formula) = Imply(
      Box(Choice(a,b), p),
      Box(Compose(Choice(Compose(a, Assign(s, Number(1))), Assign(s, Number(0))), Choice(Compose(Test(Equal(s, Number(0))), b), Compose(Test(Not(Equal(s, Number(0)))), Test(True)))), p))

    val equalReflex = proveBy("true <-> s()=s()".asFormula, equivR(1) <(cohideR(1) & byUS("= reflexive") & done, prop & done))
    equalReflex shouldBe 'proved

    val falseImplies = proveBy("true <-> (false -> p())".asFormula, prop & done)
    falseImplies shouldBe 'proved

    val notTrue = proveBy("false <-> !true".asFormula, prop & done)

    val oneIsNotZero = proveBy("false <-> 1=0".asFormula, QE() & done)

    proveBy(implementChoice("x:=2;".asProgram, "x:=3;".asProgram, "x>=2".asFormula),
      implyR(1) & choiceb(-1) & andL(-1) & composeb(1) & choiceb(1) & andR(1) <(
        composeb(1) & assignb(1, 1::Nil) & choiceb(1, 1::Nil) & composeb(1, 1::0::Nil) & testb(1, 1::0::Nil) & chase(1, 1::1::Nil) &
          useAt(oneIsNotZero, PosInExpr(1::Nil))(1, 1::0::0::Nil) & useAt(falseImplies, PosInExpr(1::Nil))(1, 1::0::Nil) &
          useAt(oneIsNotZero, PosInExpr(1::Nil))(1, 1::1::0::0::Nil) & useAt(notTrue, PosInExpr(0::Nil))(1, 1::1::0::0::Nil) &
          useAt("!! double negation")(1, 1::1::0::Nil) & useAt("true->", PosInExpr(0::Nil))(1, 1::1::Nil) &
          useAt("true&", PosInExpr(0::Nil))(1, 1::Nil) & closeId
        ,
        assignb(1) & choiceb(1) & andR(1) <(
          composeb(1) & testb(1) & useAt(equalReflex, PosInExpr(1::Nil))(1, 0::Nil) & useAt("true->")(1) & closeId
          ,
          composeb(1) & testb(1) & useAt(equalReflex, PosInExpr(1::Nil))(1, 0::0::Nil) &
            useAt(notTrue, PosInExpr(1::Nil))(1, 0::Nil) &
            useAt(falseImplies, PosInExpr(1::Nil))(1) & close
        )
      )) shouldBe 'proved
  }

  it should "generate obstacle monitor program" in withMathematica { tool =>
    val compileEqualityTest = proveBy("<?f_()=g_();>p_(||) <-> <if (f_()=g_()) { ?p_(||); } else { ?false; }>true".asFormula, chase(1, 0::Nil) & chase(1, 1::Nil) & prop & done)
    compileEqualityTest shouldBe 'proved

    val compileTest =  proveBy("<?p_();><a;>q_(||) <-> <if (p_()) { ?<a;>q_(||); } else { ?false; }>true".asFormula, testd(1, 0::Nil) & chase(1, 1::Nil) & prop & done)
    compileTest shouldBe 'proved

    val compileRegionTest = proveBy("<?p_();>true <-> <if (p_()) { ?true; } else { ?false; }>true".asFormula, testd(1, 0::Nil) & chase(1, 1::Nil) & prop & done)
    compileRegionTest shouldBe 'proved
    
    //@todo wrong sign (returns a formula with <= safe, > unsafe)
    def toMetric = "toMetric" by ((pos: Position, seq: Sequent) =>
      seq.sub(pos) match {
      case Some(Diamond(Choice(Compose(Test(p: Equal), _), Compose(Test(Not(q: Equal)), Test(False))), _)) if p==q =>
        val metric = proveBy(Equiv(False, "<margin:=1;>margin<=0".asFormula), assignd(1, 1::Nil) & QE & done)
        useAt(metric, PosInExpr(0::Nil))(pos ++ PosInExpr(0::1::1::0::Nil))
      case Some(Diamond(Choice(Compose(Test(p), Test(True)), Compose(Test(Not(q)), Test(False))), _)) if p==q =>
        val LessEqual(metric, _) = ModelPlex.toMetric(p)
        val margin = Variable("margin")
        val repl = proveBy(Imply(p, Equiv(True, Diamond(Assign(margin, metric), LessEqual(margin, Number(0))))),
          assignd(1, 1::1::Nil) & QE & done)
        useAt(repl, PosInExpr(1::0::Nil))(pos ++ PosInExpr(0::0::1::0::Nil))
    })

    val entry = KeYmaeraXArchiveParser.getEntry("Obstacle Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get

    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(entry.model.asInstanceOf[Formula],
      ("po"::"po0"::"so"::"t"::"t0"::Nil).map(Variable(_)):_*)
    val monitor = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) & ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1))
    monitor.subgoals.loneElement shouldBe "==> (0<=sopost&sopost<=S())&S()>=0&(((t0post<=tpost&t=t0post)&sopost=sopost)&po+sopost*tpost=popost+sopost*t)&po=po0post".asSequent

    val (equalities, inequalities) = FormulaTools.conjuncts(monitor.subgoals.loneElement.succ.loneElement).partition(_.isInstanceOf[Equal])
    val orderedMonitorFml = inequalities.reduceRightOption(And) match {
      case Some(ineqs) => equalities.lastOption match {
        case Some(lastEq) => equalities.updated(equalities.size-1, And(lastEq, ineqs)).reduceRight(And)
        case None => ineqs
      }
      case None => equalities.reduceRightOption(And).getOrElse(True)
    }
    orderedMonitorFml shouldBe "t=t0post&sopost=sopost&po+sopost*tpost=popost+sopost*t&po=po0post&0<=sopost&sopost<=S()&S()>=0&t0post<=tpost".asFormula
    val orderedMonitor = proveBy(monitor, useAt(proveBy(Equiv(monitor.subgoals.loneElement.succ.loneElement, orderedMonitorFml), prop & done), PosInExpr(0::Nil))(1))
    orderedMonitor.subgoals should have size 1

    val monitorAsTestsProgram = proveBy(orderedMonitor,
      RepeatTactic(ModelPlex.chaseToTests(combineTests=true)(1, PosInExpr(List.fill(equalities.size)(1))), 2) &
      ModelPlex.chaseToTests(combineTests=false)(1))
    monitorAsTestsProgram.subgoals.loneElement shouldBe "==> <?t=t0post;><?sopost=sopost;><?po+sopost*tpost=popost+sopost*t;><?po=po0post;><?((0<=sopost&sopost<=S())&S()>=0)&t0post<=tpost;>true".asSequent

    val compile = chaseCustom({
//      case Diamond(Test(False), _) => (compileFalseTest, PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil) :: Nil
      case Diamond(Test(Equal(_, _)), _) => (compileEqualityTest, PosInExpr(0::Nil), PosInExpr(0::0::1::0::Nil)::PosInExpr(0::1::1::0::Nil)::Nil) :: Nil
      case Diamond(Test(_), True) => (compileRegionTest, PosInExpr(0::Nil), Nil) :: Nil
      case _ => Nil
    })

    proveBy(monitorAsTestsProgram, compile(1) & toMetric(1) /* todo toMetric of all other tests */).subgoals.loneElement shouldBe
      "==> <?t=t0post;?<?sopost=sopost;?<?po+sopost*tpost=popost+sopost*t;?<?po=po0post;?<?((0<=sopost&sopost<=S())&S()>=0)&t0post<=tpost;?true;++?!(((0<=sopost&sopost<=S())&S()>=0)&t0post<=tpost);?false;>true;++?!po=po0post;?false;>true;++?!po+sopost*tpost=popost+sopost*t;?false;>true;++?!sopost=sopost;?false;>true;++?!t=t0post;?<margin:=1;>margin<=0;>true".asSequent
  }

  it should "prove robot contract compliance" in withMathematica { _ =>
    val entry = KeYmaeraXArchiveParser.getEntry("Robot Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._2) shouldBe 'proved)
  }

  it should "prove compatibility of obstacle and robot" in withMathematica { _ =>
    val entry = KeYmaeraXArchiveParser.getEntry("Compatibility of Obstacle and Robot",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._2) shouldBe 'proved)
  }

  it should "prove communication guarantees" in withMathematica { _ =>
    val entry1 = KeYmaeraXArchiveParser.getEntry("Communication Guarantee Safety",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry1.tactics.foreach(t => proveBy(entry1.model.asInstanceOf[Formula], t._2) shouldBe 'proved)
    val entry2 = KeYmaeraXArchiveParser.getEntry("Communication Guarantee Liveness",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry2.tactics.foreach(t => proveBy(entry2.model.asInstanceOf[Formula], t._2) shouldBe 'proved)
  }

  it should "prove system safety" in withMathematica { _ =>
    val entry = KeYmaeraXArchiveParser.getEntry("Remote-Controlled Robot System Avoids Obstacles",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    proveBy(entry.model.asInstanceOf[Formula], proveSystem(
      "stttrunning/Robot Base Case",
      "stttrunning/Robot Use Case",
      "stttrunning/Robot Step",
      "stttrunning/Obstacle Base Case",
      "stttrunning/Obstacle Use Case",
      "stttrunning/Obstacle Step",
      "stttrunning/Compatibility of Obstacle and Robot",
      "stttrunning/Communication Guarantee Safety",
      "stttrunning/Communication Guarantee Liveness"
    )(1)) shouldBe 'proved
  }

  "Robix" should "prove the robot component" in withZ3 { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/robix/robot.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/robix/robot.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove the auto-generated robot component" in withZ3 { implicit tool =>
    val model = "(t=0&v>=0&(abs(x-xoIn)>v^2/(2*B)+V*(v/B)|abs(y-yoIn)>v^2/(2*B)+V*(v/B))&dx^2+dy^2=1&A>=0&B>0&V>=0&ep>0&xoIn0=xoIn&yoIn0=yoIn&t=tOld)&true->[{{{{{{xoIn0:=xoIn;yoIn0:=yoIn;}{a:=-B;++?v=0;a:=0;w:=0;++a:=*;?-B<=a&a<=A;k:=*;w:=*;?v*k=w;?abs(x-xoIn)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yoIn)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V));}}tOld:=t;}{t'=1,x'=v*dx,y'=v*dy,dx'=-w*dy,dy'=w*dx,v'=a,w'=a*k&(t<=ep&v>=0)&t-tOld<=ep}}{xoIn:=*;?-V*(t-tOld)<=xoIn-xoIn0&xoIn-xoIn0<=V*(t-tOld);}yoIn:=*;?-V*(t-tOld)<=yoIn-yoIn0&yoIn-yoIn0<=V*(t-tOld);}?true;}*]((v>0->(x-xoIn)^2+(y-yoIn)^2>0)&true)".asFormula

    def invariant(t: String) =
      s"""v >= 0
        | & dx^2+dy^2 = 1
        | & 0 <= $t & $t <= ep
        | & -V*($t) <= xoIn-xoIn0 & xoIn-xoIn0 <= V*($t) & -V*($t) <= yoIn-yoIn0 & yoIn-yoIn0 <= V*($t)
        | & (v = 0 | abs(x-xoIn) > v^2 / (2*B) + V*(v/B)
        |          | abs(y-yoIn) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula

    def di(a: String, t: String): DependentPositionTactic = diffInvariant(
      s"0<=$t".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*($t)".asFormula,
      s"-($t) * (v - $a/2*($t)) <= x - old(x) & x - old(x) <= ($t) * (v - $a/2*($t))".asFormula,
      s"-($t) * (v - $a/2*($t)) <= y - old(y) & y - old(y) <= ($t) * (v - $a/2*($t))".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide=true)('Llast)*3 /* 3 old(...) in DI */ & (andL('_)*) &
      print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule*) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('R) & (andL('L)*) & loop(invariant("t-tOld"))('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done") & done,
      /* use case */ print("Use case...") & speculativeQE & print("Use case done") & done,
      /* induction step */ print("Induction step") & chase(1) & print("After chase") & normalize(andR) & printIndexed("After normalize") <(
      print("Braking branch") & di("-B", "t-tOld")(1) & print("After DI") & dw & print("After DW") & normalize(andR) & print("After braking normalize") & OnAll(speculativeQE) & print("Braking branch done") & done,
      print("Stopped branch") & di("0", "t-tOld")(1) & print("After DI") & dw & print("After DW") & normalize(andR) & OnAll(speculativeQE) & print("Stopped branch done") & done,
      print("Acceleration branch") & hideL('L, "v=0|abs(x-xoIn)>v^2/(2*B)+V*(v/B)|abs(y-yoIn)>v^2/(2*B)+V*(v/B)".asFormula) &
        di("a", "t-tOld")(1) & print("After DI") & dw & print("After DW") & normalize & print("After acc normalize") & OnAll(hideFactsAbout("dx", "dy", "k", "k_0") partial) <(
        hideFactsAbout("y", "yoIn", "yoIn0") & accArithTactic & done,
        hideFactsAbout("x", "xoIn", "xoIn0") & accArithTactic & done
        ) & print("Acceleration branch done")
      ) & print("Induction step done") & done
      ) & print("Proof done") & done
    proveBy(model, tactic) shouldBe 'proved
  }

  it should "prove the obstacle component" in withZ3 { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/robix/obstacle.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/robix/obstacle.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove compatibility" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/robix/compatibility.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove monolithic model" in withZ3 { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/robix/system.kyx"))

    val invariant =
      """v >= 0
        | & dx^2+dy^2 = 1
        | & xo = xor & yo = yor
        | & (v = 0 | abs(x-xo) > v^2 / (2*B()) + V()*(v/B())
        |          | abs(y-yo) > v^2 / (2*B()) + V()*(v/B()))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "0<=t".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V() <= xo - old(xo) & xo - old(xo) <= t * V()".asFormula,
      "-t * V() <= yo - old(yo) & yo - old(yo) <= t * V()".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide=true)('Llast)*5 /* 5 old(...) in DI */ & (andL('_)*) &
      print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule*) & printIndexed("Before replaceTransform") &
      //@todo auto-transform
      replaceTransform("ep".asTerm, "t".asTerm)(-8) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & (andL('_)*) & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & chase(1) & normalize(andR) & printIndexed("After normalize") <(
      print("Braking branch 1") & di("-B()")(1) & dw & prop & OnAll((cohide(1) & byUS("= reflexive")) | skip) & OnAll(speculativeQE) & print("Braking branch 1 done"),
      print("Braking branch 2") & di("-B()")(1) & dw & prop & OnAll((cohide(1) & byUS("= reflexive")) | skip) & OnAll(speculativeQE) & print("Braking branch 2 done"),
      print("Stopped branch 1") & di("0")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Stopped branch 1 done"),
      print("Acceleration branch 1") & hideL('L, "v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())|abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) &
        di("a")(1) & dw & prop & OnAll((cohide(1) & byUS("= reflexive")) | skip) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0")) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch 1 done"),
      print("Stopped branch 1") & di("0")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Stopped branch 2 done"),
      print("Acceleration branch 2") & hideL('L, "v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())|abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) &
        di("a")(1) & dw & prop & OnAll((cohide(1) & byUS("= reflexive")) | skip) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0")) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch 2 done")
      ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  "Multiport local lane control" should "prove the leader component" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_leader.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove the follower component" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_follower.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_follower.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove compatibility" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_compatibility.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove the monolithic system" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_system.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_system.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  "ETCS" should "prove RBC component" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/etcs/multiport_rbc.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove train component" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/etcs/multiport_train.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove compatibility" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/etcs/multiport_compatibility.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

}
