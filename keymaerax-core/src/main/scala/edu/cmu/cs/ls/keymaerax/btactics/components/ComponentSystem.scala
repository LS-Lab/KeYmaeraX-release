package edu.cmu.cs.ls.keymaerax.btactics.components

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.List

/**
  * Tactic to prove system safety from isolated component and compatibility proofs.
  *
  * @see Andreas Müller, . [[https://doi.org/10.1007/s10009-018-0502-9 Tactical contract composition for hybrid system component verification]]. STTT, Special issue for selected papers from FASE'17, 2018.
  * @author Stefan Mitsch     
  */
object ComponentSystem {
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
  def programIndependence(swapCompose: Boolean = true): DependentPositionTactic = "programIndependence" by ((pos: Position, seq: Sequent) => {
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
      case Some(Box(Compose(a,b), p)) if swapCompose =>
        composeb(pos) & programIndependence(swapCompose=false)(pos) & useAt("[;] compose", PosInExpr(1::Nil))(pos)
      case Some(Box(a, Box(b, p))) =>
        val prgVars = StaticSemantics.freeVars(p).intersect(StaticSemantics.boundVars(a) ++ StaticSemantics.boundVars(b)).
          toSet[Variable].toList.sorted[NamedSymbol]

        val dots = prgVars.zipWithIndex.map({ case (v,i) => v -> DotTerm(Real, Some(i)) })
        val args = prgVars.reduceOption(Pair).getOrElse(Nothing)
        val q = PredOf(Function("q_", None, args.sort, Bool), args)

        val swapped = proveBy(Equiv(Box(b, Box(a, q)), Box(a, Box(b, q))),
          chase(1, 0::Nil) & chase(1, 1::Nil) & equivR(1) &
            OnAll(
              SaturateTactic(OnAll(allR(1) | prop)) &
                Idioms.?(OnAll(SaturateTactic(implyL('L) <(prop, nil) | allL('L)) & prop & done))
            )
        )
        val rensubst = (_: Option[Subst]) => RenUSubst(
          dots.map({ case (v,d) => d->v }) :+
            (dots.foldLeft[Formula](q)({ case (qq, (v,d)) => qq.replaceAll(v, d) }) -> dots.foldLeft(p)({ case (pp, (v,d)) => pp.replaceFree(v, d) }))
        )
        useAt(swapped, PosInExpr(1::Nil), rensubst)(pos)
    }
  })

  /** STTT Lemma 2 */
  lazy val dropControl: DependentPositionTactic = "dropControl" by ((pos: Position, seq: Sequent) => {
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
  def dropPlant(keep: Set[Variable]): DependentPositionTactic = "dropPlant" by ((pos: Position, seq: Sequent) => {
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
  def overapproximateProgram: DependentPositionTactic = "overapproximateProgram" by ((pos: Position, seq: Sequent) => {
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

  def introduceTest(f: Formula): DependentPositionTactic = "introduceTest" by ((pos: Position, seq: Sequent) => {
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

  def weakenTest(f: Formula): DependentPositionTactic = "weakenTest" by ((pos: Position, seq: Sequent) => {
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
        programIndependence()(pos.topLevel ++ pos.inExpr.parent) & programIndependence()(pos) & DebuggingTactics.print("Moved test") &
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
      else if (programs.head == Test(True) && programs.tail.isEmpty) Nil
      else {
        val (p1, tail) = programs.span({ case _: Test => false case _ => true })
        (p1.reduce(Compose) -> tail.head.asInstanceOf[Test]) +: ports(tail.tail)
      }
    }
    ports(atoms(program))
  }

  /** STTT Fig. 13 */
  private def justifyFout(fout: Formula, keepPlantVars: Set[Variable], c1toC2comGuaranteeLiveness: Lemma, c2use: Lemma, c2step: Lemma) = "justifyFout" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(_: Imply) =>
      val Imply(_ , Box(_, Box(_, Box(_, Box(_, foutSafety))))) = fout
      val Box(Compose(_, Compose(_, Compose(_, Compose(plant2, Compose(in2, cp2))))), c2inv) = c2step.fact.conclusion.succ.head

      DebuggingTactics.print("Justify Fout") &
        cohideOnlyR(pos) &
        (if (foutSafety == True) implyR(1) & abstractionb(1, 1::1::1::Nil) & abstractionb(1, 1::1::Nil) &
          abstractionb(1, 1::Nil) & abstractionb(1) & closeT
        else dropPlant(keepPlantVars)(1, 1::1::1::1::Nil) & DebuggingTactics.print("Dropped plant1") &
          composeb(1, 1::1::Nil) & dropControl(1, 1::1::Nil) & DebuggingTactics.print("Dropped ctrl1") &
          composeb(1, 1::Nil) & dropControl(1, 1::Nil) & DebuggingTactics.print("Dropped delta1") &
          cutAt(Diamond(Compose(in2, cp2), foutSafety))(1, 1::1::1::1::1::Nil) <(
            // use
            useAt(DerivedAxioms.boxDiamondSubstPropagation, PosInExpr(1::1::Nil))(1, 1::1::1::1::1::Nil) <(
              DebuggingTactics.print("Strengthen") & /* todo: hide all non-const factcs */ hideL(-1) /* End todo */ &
                generalize(c2inv)(1, 1::1::1::1::1::Nil) <(
                  DebuggingTactics.print("Close by C2 induction step") &
                    boxAnd(1, 1::1::1::1::Nil) & abstractionb(1, 1::1::1::1::0::Nil) &
                    boxAnd(1, 1::1::1::Nil) & abstractionb(1, 1::1::1::0::Nil) &
                    boxAnd(1, 1::1::Nil) & abstractionb(1, 1::1::0::Nil) &
                    boxAnd(1, 1::Nil) & abstractionb(1, 1::0::Nil) &
                    implyR(1) & andR(1) <(prop, nil) &
                    DebuggingTactics.print("Generalized C2 induction step") &
                    cutAt(Box(plant2, Box(Compose(in2, cp2), c2inv)))(1, 1::1::1::Nil) & DebuggingTactics.print("Cut, now what?") <(
                    useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::1::Nil) &
                      useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::Nil) &
                      useAt("[;] compose", PosInExpr(1::Nil))(1, 1::Nil) &
                      useAt("[;] compose", PosInExpr(1::Nil))(1) &
                      useLemma(c2step, Some(prop)) &
                      DebuggingTactics.done("Close by C2 induction step")
                    ,
                    DebuggingTactics.print("Proving C2 diff. refine") & cohideR(1) & CMon(1, 1::1::1::1::Nil) &
                      useAt(DerivedAxioms.DiffRefine, PosInExpr(1::Nil))(1) &
                      dW(1) & prop & DebuggingTactics.done("Proving C2 diff. refine")
                  )
                  ,
                  DebuggingTactics.print("Close by C2 use case") & useLemma(c2use, Some(prop)) & DebuggingTactics.done("Close by C2 use case")
                )
              ,
              DebuggingTactics.print("Close by communication guarantee liveness") &
                implyR(1) & ((abstractionb(1) & SaturateTactic(allR(1)))*4) &
                //@todo use communication guarantees of internal ports
                composed(1) & testd(1, 1::Nil) & useAt(DerivedAxioms.trueAnd)(1, 1::Nil) &
                useLemma(c1toC2comGuaranteeLiveness, Some(prop)) & DebuggingTactics.done("Close by communication guarantee liveness")
            )
            ,
            // show
            DebuggingTactics.print("Show InCp") & cohideR(1) &
              CMon(1, 1::1::1::1::1::1::Nil) & implyR(1) & useAt("<> diamond", PosInExpr(1::Nil))(-1) & notL(-1) &
              abstractionb(2) & prop & DebuggingTactics.done("Show InCp")
          )
          ) & DebuggingTactics.done("Justify Fout")
  })

  /** STTT Fig. 11: Component 1 */
  private def proveSystemCompStep(c1step: Lemma, c2use: Lemma, c2step: Lemma,
                                  compatibility: Lemma, c1toc2comGuaranteeLiveness: Lemma, fout: Formula) = "proveSystemCompStepC1" by ((pos: Position, seq: Sequent) => {
    require(pos.isTopLevel)
    seq.sub(pos) match {
      case Some(Box(delta3, Box(Compose(ctrl1,ctrl2), Box(rememberStart@Assign(told, t), Box(ODESystem(DifferentialProduct(time, plant3), q3), Box(Compose(in3,cp3), inv1)))))) =>
        val Box(Compose(delta1, Compose(_/*ctrl1*/, Compose(_/*rememberStart*/, Compose(plant1, Compose(in1, cp1))))), _) = c1step.fact.conclusion.succ.head

        val Compose(_,in2) = in3

        val piouts = fout match {
          case Imply(_, Box(delta, Box(ctrl, Box(remember, Box(plant, pi2Out))))) => FormulaTools.leftConjuncts(pi2Out)
        }

        val plant1Vars = StaticSemantics.boundVars(plant1).toSet.filter(_.isInstanceOf[BaseVariable])
        val plant2Vars = (StaticSemantics.boundVars(plant3).toSet.filter(_.isInstanceOf[BaseVariable]) -- plant1Vars) ++
          StaticSemantics.boundVars(time).toSet.filter(_.isInstanceOf[BaseVariable])

        val Compose(_, Compose(_, con)) = cp3
        val connections = leftAssignments(con, piouts.size)
        val conStaticSem = connections.map(p => StaticSemantics.boundVars(p) -> StaticSemantics.freeVars(p)).toMap
        val connectedVars = connections.flatMap(StaticSemantics.boundVars(_).toSet).toSet

        val in1cons = ports(in1).filter({ case (port, pin) => !StaticSemantics.boundVars(port).intersect(connectedVars).isEmpty })
        val in1Assumptions = in1cons.map({ case (port, pin) => StaticSemantics.boundVars(port).toSet -> pin.cond }).toMap
        val guarantees = in1cons.map({ case (port, _) =>
          StaticSemantics.boundVars(port).toSet ->
            piouts.find(piout => !conStaticSem(StaticSemantics.boundVars(port)).intersect(StaticSemantics.freeVars(piout)).isEmpty).getOrElse(True) }).toMap

        DebuggingTactics.print("Disassembling system into components") &
          cut(fout) <(
            // use
            //@todo S2.2 reorder to in1^*;in2^* (for now: assume they are in the right order)
            (4 to 6).map(i => PosInExpr(List.fill(i)(1))).map(i => composeb(pos ++ i)).reduce[BelleExpr](_&_) &
              composeb(pos ++ PosInExpr(List.fill(4)(1))) & // decompose in3 into [in1*][in2*]
              // Step 2.3 (move con between in1* and in2*)
              (5 to 7).map(i => PosInExpr(List.fill(i)(1))).reverse.map(programIndependence(false)(1, _)).reduce[BelleExpr](_&_) &
              DebuggingTactics.print("Step 2.3 done") &
              // Step 2.4 (drop cp2)
              dropControl(pos ++ PosInExpr(List.fill(7)(1))) & DebuggingTactics.print("Step 2.4 done") &
              // Step 2.5 (drop in2*)
              dropControl(pos ++ PosInExpr(List.fill(5)(1))) & DebuggingTactics.print("Step 2.5 done") &
              // Steps 2.6-2.11, note that reserved time `t` is present in contract models but not part of the plant per STTT
              proveSystemCompStep4(in1Assumptions, guarantees, plant1Vars.filter(_.name != "t"), compatibility, in1cons.size)(pos ++ PosInExpr(List.fill(5)(1))) &
              (if (ports(in2).nonEmpty) abstractionb(pos ++ PosInExpr(List.fill(5)(1))) else skip) &
              DebuggingTactics.print("Steps 2.6-2.11 done") &
              dropPlant(plant1Vars)(pos ++ PosInExpr(1::1::1::Nil)) & DebuggingTactics.print("Step 2.12 done") &
              composeb(pos ++ PosInExpr(1::Nil)) & dropControl(pos ++ PosInExpr(1::1::Nil)) & // drop ctrl2
              composeb(pos) & dropControl(pos ++ PosInExpr(1::Nil)) & DebuggingTactics.print("Step 2.13 done") & // drop delta2
              hideL('Llast) &
              // use step lemma
              ("ANON" by ((pp: Position, ss: Sequent) => ss.sub(pp) match {
                case Some(have@Box(_, p)) =>
                  useAt(proveBy(Equiv(Box(in1, p), have), chase(1, 0::Nil) & chase(1, 1::Nil) & QE), PosInExpr(1::Nil))(pp)
              }))(pos ++ PosInExpr(1::1::1::1::Nil)) &
              DebuggingTactics.print("Using step lemma") &

              cutAt(Box(plant1, Box(Compose(in1, cp1), inv1)))(1, 1::1::1::Nil) <(
                useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::1::Nil) &
                  useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::Nil) &
                  useAt("[;] compose", PosInExpr(1::Nil))(1, 1::Nil) &
                  useAt("[;] compose", PosInExpr(1::Nil))(1) &
                  useLemma(c1step, Some(prop)) &
                  DebuggingTactics.done("Close by C1 induction step")
                ,
                DebuggingTactics.print("Proving C1 diff. refine") & cohideR(1) & CMon(1, 1::1::1::1::Nil) &
                  composeb(1, 0::1::Nil) & useAt(DerivedAxioms.DiffRefine, PosInExpr(1::Nil))(1) &
                  dW(1) & prop & DebuggingTactics.done("Proving C1 diff. refine")
              ) &
              DebuggingTactics.print("Step done") & DebuggingTactics.done("Step")
            ,
            // show
            justifyFout(fout, plant2Vars, c1toc2comGuaranteeLiveness, c2use, c2step)('Rlast)
          ) & DebuggingTactics.print("Done disassembling system into components") & DebuggingTactics.done("Disassembling system into components")
    }
  })

  /** STTT Fig. 10 */
  private def proveSystemStep(c1use: Lemma, c1step: Lemma,
                              c2use: Lemma, c2step: Lemma,
                              pi1Out: Formula, pi2Out: Formula,
                              compatibility: Lemma,
                              c1toc2comGuaranteeSafety: Lemma, c1toc2comGuaranteeLiveness: Lemma,
                              c2toc1comGuaranteeSafety: Lemma, c2toc1comGuaranteeLiveness: Lemma) = "proveSystemStep" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(Compose(delta3, Compose(ctrl3, Compose(rememberStart@Assign(told, t), Compose(plant3@ODESystem(DifferentialProduct(_, _), q3), Compose(in3, Compose(cp1, Compose(cp2, con))))))), inv3@And(inv1, And(inv2, zeta)))) =>
      //@todo check program shapes in lemmas
      val cr1 :: cr2 :: Nil = (0 to 3) :: (4 to 6) :: Nil

      DebuggingTactics.print("Proving component loops and communication guarantees") &
        boxAnd(1) & andR(1) <(
        // inv1
        DebuggingTactics.print("Proving inv1") &
          cr1.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
          proveSystemCompStep(c1step, c2use, c2step, compatibility, c1toc2comGuaranteeLiveness, Imply(inv2, Box(delta3, Box(ctrl3, Box(rememberStart, Box(plant3, pi2Out))))))(pos) &
          DebuggingTactics.print("Done proving inv1") & DebuggingTactics.done("Proving inv1")
        ,
        boxAnd(1) & andR(1) <(
          // inv2
          DebuggingTactics.print("Proving inv2") &
            cr1.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
            DebuggingTactics.print("Reordering components") &
            programIndependence()(1) & // swap delta 
            programIndependence()(1, 1::Nil) & // swap controllers
            composeb(1, 1::1::1::1::Nil) &
            programIndependence()(1, 1::1::1::1::Nil) & // swap ports
            composeb(1, 1::1::1::1::1::Nil) &
            composeb(1, 1::1::1::1::1::1::Nil) &
            programIndependence()(1, 1::1::1::1::1::Nil) & // swap internal connections
            useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::1::1::1::1::Nil) &
            useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::1::1::1::Nil) &
            useAt("[;] compose", PosInExpr(1::Nil))(1, 1::1::1::1::Nil) &
            DebuggingTactics.print("Done reordering components") &
            proveSystemCompStep(c2step, c1use, c1step, compatibility, c2toc1comGuaranteeLiveness, Imply(inv1, Box(delta3, Box(ctrl3, Box(rememberStart, Box(plant3, pi1Out))))))(pos) &
            DebuggingTactics.print("Done proving inv2") & DebuggingTactics.done("Proving inv2")
          ,
          // zeta
          DebuggingTactics.print("Proving communication guarantee (zeta step)") &
            cr1.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
            cr2.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
            (cr1.head to cr2.last).map(i => PosInExpr(List.fill(i)(1))).reverse.map(abstractionb(1, _)).reduce[BelleExpr](_ & _) &
            (allR(1)*) & cohideR(1) & by(c2toc1comGuaranteeSafety) &
            DebuggingTactics.print("Done proving communication guarantee (zeta step)") &
            DebuggingTactics.done("Proving communication guarantee (zeta step)")
        )
      ) & DebuggingTactics.print("Done proving component loops and communication guarantees") & DebuggingTactics.done("Proving component loops and communication guarantees")
  })

  /** STTT Fig. 9 */
  private def proveSystem(c1base: Lemma, c1use: Lemma, c1step: Lemma,
                          c2base: Lemma, c2use: Lemma, c2step: Lemma,
                          compatibility: Lemma,
                          c1toc2comGuaranteeSafety: Lemma, c1toc2comGuaranteeLiveness: Lemma,
                          c2toc1comGuaranteeSafety: Lemma, c2toc1comGuaranteeLiveness: Lemma) = "proveSystem" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
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
        proveSystemStep(
          c1use, c1step,
          c2use, c2step,
          pi1Out, pi2Out,
          compatibility,
          c1toc2comGuaranteeSafety, c1toc2comGuaranteeLiveness,
          c2toc1comGuaranteeSafety, c2toc1comGuaranteeLiveness)(1)
      )
  })

  /** Proves system safety from isolated component and compatibility proofs. */
  def proveSystem(c1baseLemma: String, c1useLemma: String, c1stepLemma: String,
                  c2baseLemma: String, c2useLemma: String, c2stepLemma: String,
                  compatibilityLemma: String,
                  c1toc2comGuaranteeSafetyLemma: String,
                  c1toc2comGuaranteeLivenessLemma: String,
                  c2toc1comGuaranteeSafetyLemma: String,
                  c2toc1comGuaranteeLivenessLemma: String): DependentPositionTactic = {
    proveSystem(
      LemmaDBFactory.lemmaDB.get("user/" + c1baseLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c1useLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c1stepLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c2baseLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c2useLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c2stepLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + compatibilityLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c1toc2comGuaranteeSafetyLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c1toc2comGuaranteeLivenessLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c2toc1comGuaranteeSafetyLemma).get,
      LemmaDBFactory.lemmaDB.get("user/" + c2toc1comGuaranteeLivenessLemma).get
    )
  }
}
