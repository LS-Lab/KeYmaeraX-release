package edu.cmu.cs.ls.keymaerax.btactics.components

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core.{And, Compose, _}
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.List
import scala.reflect.runtime.universe

/**
  * Tactic to prove system safety from isolated component and compatibility proofs.
  *
  * @see Andreas Müller, . [[https://doi.org/10.1007/s10009-018-0502-9 Tactical contract composition for hybrid system component verification]]. STTT, Special issue for selected papers from FASE'17, 2018.
  * @author Stefan Mitsch     
  */
object ComponentSystem extends TacticProvider {
  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) = (ComponentSystem.getClass, universe.typeOf[ComponentSystem.type])

  private val namespace = "components"

  /** STTT Lemma 1 Corollaries */
  private lazy val assignmentIndependence1 = AnonymousLemmas.remember(
    "[x_:=s_();][y_:=t_();]p_(x_,y_) <-> [y_:=t_();][x_:=s_();]p_(x_,y_)".asFormula,
    master() & done,
    namespace
  )
  private lazy val assignmentIndependence2 = AnonymousLemmas.remember(
    "[x_:=*;][y_:=t_();]p_(x_,y_) <-> [y_:=t_();][x_:=*;]p_(x_,y_)".asFormula,
    master() & allL('Llast) & id & done,
    namespace
  )
  private lazy val assignmentIndependence3 = AnonymousLemmas.remember(
    "[x_:=*;][y_:=*;]p_(x_,y_) <-> [y_:=*;][x_:=*;]p_(x_,y_)".asFormula,
    master() & prop & done,
    namespace
  )
  private lazy val assignmentIndependence4 = AnonymousLemmas.remember(
    "[x_:=s_();][?q_();]p_(x_) <-> [?q_();][x_:=s_();]p_(x_)".asFormula,
    master() & prop & done,
    namespace
  )
  private lazy val assignmentIndependence5 = AnonymousLemmas.remember(
    "[x_:=*;][?q_();]p_(x_) <-> [?q_();][x_:=*;]p_(x_)".asFormula,
    chase(1, 0::Nil) & chase(1, 1::Nil) & equivR(1) <(
      implyR(1) & allR(1) & allL(-1) & prop & done,
      allR(1) & implyR(1) & implyL(-1) <(id, allL(-1) & id) & done
    ) & done,
    namespace
  )
  private lazy val testIndependence = AnonymousLemmas.remember(
    "[?q_();][?r_();]p_() <-> [?r_();][?q_();]p_()".asFormula,
    master() & prop & done,
    namespace
  )

  /** STTT Lemma 1 */
  def programIndependence(swapCompose: Boolean = true): DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
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
        composeb(pos) & programIndependence(swapCompose=false)(pos) & useAt(Ax.composeb, PosInExpr(1::Nil))(pos)
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
      case Some(e) => throw new TacticInapplicableFailure("programIndepedence only applicable to box properties, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
  })

  /** STTT Lemma 2 */
  lazy val dropControl: DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
    require(pos.isSucc, "Drop control only in succedent")
    val lemma2 = seq.sub(pos) match {
      case Some(have@Box(a, Box(b, p))) if
      StaticSemantics.freeVars(p).intersect(StaticSemantics.boundVars(b)).isEmpty &&
        StaticSemantics.freeVars(a).intersect(StaticSemantics.boundVars(b)).isEmpty =>
        proveBy(Imply(Box(a, p), have), implyR(1) & monb & abstractionb(1) & id & done)
      case Some(have@Box(b, Box(a, p))) if
      StaticSemantics.freeVars(p).intersect(StaticSemantics.boundVars(b)).isEmpty &&
        StaticSemantics.freeVars(a).intersect(StaticSemantics.boundVars(b)).isEmpty =>
        proveBy(Imply(Box(a, p), have), implyR(1) & abstractionb(1) & id & done)
      case Some(have@Box(a, p)) if
      p.isFOL &&
        StaticSemantics.freeVars(p).intersect(StaticSemantics.boundVars(a)).isEmpty &&
        StaticSemantics.freeVars(a).intersect(StaticSemantics.boundVars(a)).isEmpty =>
        proveBy(Imply(p, have), implyR(1) & abstractionb(1) & id & done)
      case Some(e) => throw new TacticInapplicableFailure("dropControl only applicable to box properties, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
    useAt(lemma2, PosInExpr(1::Nil))(pos)
  })

  /** STTT Lemma 3 */
  def dropPlant(keep: Set[Variable]): DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
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
          case Some(xsys) if StaticSemantics.boundVars(xsys).toSet.exists(_.name != "t") =>
            ys.reduceOption(DifferentialProduct.apply) match {
              case Some(ysys) =>
                val universalXClosure = ys.map(_.xp.x).foldLeft[Formula](Box(ODESystem(ode, h), p))((f, y) => Forall(y::Nil, f))
                val partitionedOdeLemma =
                  proveBy(Imply(Box(ODESystem(DifferentialProduct(ysys, xsys), h), p), Box(ODESystem(ode, h), p)),
                    implyR(1) &
                      //sort ys into reverse order because we apply DGi outside in (innermost universal quantifier first)
                      AxiomaticODESolver.selectionSort(h, p, ode, ys.map(_.xp.x)++xs.map(_.xp.x), SuccPosition(1)) &
                      id)
                proveBy(Imply(Box(ODESystem(xsys, h), p), have),
                  implyR(1) & DifferentialTactics.diffRefine(h)(1) <(
                    cut(universalXClosure) <(
                      allL('Llast)*ys.size & id & done
                      ,
                      hideR(1) & useAt(partitionedOdeLemma, PosInExpr(1::Nil))(1, List.fill(ys.size)(0)) &
                        ys.indices.reverse.
                          map(i => PosInExpr(List.fill(i)(0))).
                          map(useAt(Ax.DGi, PosInExpr(1::Nil))(1, _)).
                          reduceOption[BelleExpr](_ & _).getOrElse(skip) &
                        id & done
                    ),
                    cohideR(1) & dW(1) & prop & done
                  )
                )
              case None => proveBy(Equiv(have, have), byUS(Ax.equivReflexive))
            }
          case Some(xsys) if StaticSemantics.boundVars(xsys).toSet.forall(_.name == "t") =>
            ys.reduceOption(DifferentialProduct.apply) match {
              case Some(ysys) => ???
              case None => proveBy(Equiv(have, have), byUS(Ax.equivReflexive))
            }
          case None =>
            ys.reduceOption(DifferentialProduct.apply) match {
              case Some(ysys) =>
                val universalXClosure = ys.map(_.xp.x).foldLeft[Formula](Box(ODESystem(ode, h), p))((f, y) => Forall(y::Nil, f))
                val partitionedOdeLemma =
                  proveBy(Imply(Box(ODESystem(ysys, h), p), Box(ODESystem(ode, h), p)),
                    implyR(1) &
                      //sort ys into reverse order because we apply DGi outside in (innermost universal quantifier first)
                      AxiomaticODESolver.selectionSort(h, p, ode, ys.map(_.xp.x)++xs.map(_.xp.x), SuccPosition(1)) &
                      id)
                proveBy(Imply(Box(Test(h), p), have),
                  implyR(1) & DifferentialTactics.diffRefine(h)(1) <(
                    cut(universalXClosure) <(
                      allL('Llast)*ys.size & id & done
                      ,
                      hideR(1) & useAt(partitionedOdeLemma, PosInExpr(1::Nil))(1, List.fill(ys.size)(0)) &
                        allR(1)*ys.size & dW(1) & useAt(Ax.testb, PosInExpr(1::Nil))(1) &
                        id & done
                    ),
                    cohideR(1) & dW(1) & prop & done
                  )
                )
              case None => proveBy(Equiv(have, have), byUS(Ax.equivReflexive))
            }
        }
      case Some(e) => throw new TacticInapplicableFailure("Lemma 3 only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
    useAt(lemma3, PosInExpr(1::Nil))(pos)
  })

  /** STTT Lemma 4 */
  def overapproximateProgram: DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(have@Box(a, p)) =>
        val abv = StaticSemantics.boundVars(a).intersect(StaticSemantics.freeVars(p)).toSet.toList
        val approximate = abv.indices.reverse.
          map(i => PosInExpr(List.fill(i)(0))).
          map(useAt(Ax.randomb, PosInExpr(1::Nil))(1, _)).reduceOption[BelleExpr](_ & _).getOrElse(skip)
        val decompose = Range(0, abv.size-1).
          map(i => PosInExpr(List.fill(i)(1))).
          map(useAt(Ax.composeb)(-1, _)).reduceOption[BelleExpr](_ & _).getOrElse(skip)
        val lemma4 = proveBy(
          Imply(Box(abv.map(AssignAny).reduceRightOption(Compose).getOrElse(Test(True)), p), have),
          implyR(1) & abstractionb(1) & approximate & decompose & id)
        useAt(lemma4, PosInExpr(1::Nil))(pos)
      case Some(e) => throw new TacticInapplicableFailure("higherdV only applicable to box properties, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
  })

  /** STTT Lemma 5 */
  private lazy val introduceTestLemma = AnonymousLemmas.remember(
    "[a{|^@|};]q(||) -> ([a{|^@|};][?q(||);]p(||) <-> [a{|^@|};]p(||))".asFormula,
    implyR(1) & equivR(1) <(
      testb(-2, 1::Nil),
      testb(1, 1::Nil)
    ) & onAll(implyRi()(-2, 1) & useAt(Ax.K, PosInExpr(1::Nil))(1) & monb & prop & done), namespace)

  def introduceTest(f: Formula): DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(a, p)) =>
        val subst = (_: Option[Subst]) => RenUSubst(
          SystemConst("a") -> a ::
            "p(||)".asFormula -> p ::
            "q(||)".asFormula -> f :: Nil
        )
        useAt(introduceTestLemma, PosInExpr(1::1::Nil), subst)(pos)
      case Some(e) => throw new TacticInapplicableFailure("introduceTest only applicable to box properties, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
  })

  /** STTT Lemma 6 */
  private lazy val weakenTestLemma = AnonymousLemmas.remember(
    "(r_() -> q_()) -> [?q_();]p_() -> [?r_();]p_()".asFormula,
    testb(1, 1::0::Nil) & testb(1, 1::1::Nil) & prop & done,
    namespace)

  def weakenTest(f: Formula): DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(Test(r), p)) =>
        val subst = (_: Option[Subst]) => RenUSubst(
          "r_()".asFormula -> r ::
            "p_()".asFormula -> p ::
            "q_()".asFormula -> f :: Nil
        )
        useAt(weakenTestLemma, PosInExpr(1::1::Nil), subst)(pos)
      case Some(e) => throw new TacticInapplicableFailure("weakenTest only applicable to box tests, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
  })

  /** STTT Fig. 12 */
  private def useCompatibility(compatibility: Lemma, plant1Vars: Set[Variable]) = anon ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(delta, Box(ctrl, Box(Assign(told,t), Box(plant, Box(in1star, Box(cons, Imply(pi2out, pi1in)))))))) =>
      DebuggingTactics.print("Using compatibility") &
      useAt(compatibility, PosInExpr(1::Nil))(pos ++ PosInExpr(List.fill(5)(1))) & DebuggingTactics.print("Applied compatibility lemma") &
        dropControl(pos ++ PosInExpr(1::1::1::1::Nil)) &
        dropPlant(plant1Vars)(pos ++ PosInExpr(1::1::1::Nil)) &
        dropControl(pos ++ PosInExpr(1::1::Nil)) &
        dropControl(pos ++ PosInExpr(1::Nil)) &
        dropControl(pos) & DebuggingTactics.print("Dropped all statements except port memory") &
        chase(1) & prop & DebuggingTactics.done("Fig. 12 done")
    case Some(e) => throw new TacticInapplicableFailure("Fig. 12 only applicable to box properties, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
  })
  
  /** Communication liveness for empty connections */
  private lazy val emptyConLiveness = AnonymousLemmas.remember("<?true;>true".asFormula, testd(1) & prop, namespace)

  private def proveSystemCompStep4(inputAssumptions: Map[Set[Variable],Formula], outputGuarantees: Map[Set[Variable],Formula],
                                   plant1Vars: Set[Variable],
                                   compatibility: Lemma, remainingCons: Int): DependentPositionTactic = anon ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(_) if remainingCons <= 0 => skip
    case Some(Box(cons, _)) if remainingCons > 0 =>
      val headConVars: Set[Variable] = leftAssignments(cons, remainingCons).flatMap(p => StaticSemantics.boundVars(p).toSet).toSet
      (if (remainingCons > 1) composeb(pos) else skip) &
        // Step 2.7 (introduce output guarantee of component 2)
        introduceTest(outputGuarantees(headConVars))(pos.topLevel ++ pos.inExpr.parent.parent) <(skip, prop & DebuggingTactics.done("Step 2.7")) & DebuggingTactics.print("Introduced test") &
        // Step 2.8 (move output guarantee past connection)
        programIndependence()(pos.topLevel ++ pos.inExpr.parent) & programIndependence()(pos) & DebuggingTactics.print("Moved test") &
        // Step 2.9 (weaken output guarantee to input assumption)
        weakenTest(inputAssumptions(headConVars))(pos ++ PosInExpr(1::Nil)) <(
          skip,
          useCompatibility(compatibility, plant1Vars)(pos.topLevel)
        ) & DebuggingTactics.print("Weakened test") &
        // Step 2.10
        overapproximateProgram(pos) & DebuggingTactics.print("Overapproximated program") &
        // Step 2.11
        useAt(Ax.composeb, PosInExpr(1::Nil))(pos) & useAt(Ax.composeb, PosInExpr(1::Nil))(pos.topLevel ++ pos.inExpr.parent) &
        // recurse until done
        proveSystemCompStep4(inputAssumptions, outputGuarantees, plant1Vars, compatibility, remainingCons-1)(pos)
    case Some(e) => throw new TacticInapplicableFailure("proveSystemCompStep4 only applicable to box properties, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
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
  private def justifyFout(fout: Formula, keepPlantVars: Set[Variable], comGuaranteeLiveness: Lemma, c2use: Lemma, c2step: Lemma) = anon ((pos: Position, seq: Sequent) => seq.sub(pos) match {
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
            useAt(Ax.boxDiamondSubstPropagation, PosInExpr(1::1::Nil))(1, 1::1::1::1::1::Nil) <(
              DebuggingTactics.print("Strengthen") & /* todo: hide all non-const factcs */ hideL(-1) /* End todo */ &
                generalize(c2inv)(1, 1::1::1::1::1::Nil) <(
                  DebuggingTactics.print("Close by C2 induction step") &
                    boxAnd(1, 1::1::1::1::Nil) & abstractionb(1, 1::1::1::1::0::Nil) &
                    boxAnd(1, 1::1::1::Nil) & abstractionb(1, 1::1::1::0::Nil) &
                    boxAnd(1, 1::1::Nil) & abstractionb(1, 1::1::0::Nil) &
                    boxAnd(1, 1::Nil) & abstractionb(1, 1::0::Nil) &
                    implyR(1) & andR(1) <(prop, nil) &
                    DebuggingTactics.print("Generalized C2 induction step") &
                    cutAt(Box(plant2, Box(Compose(in2, cp2), c2inv)))(1, 1::1::1::Nil) <(
                    useAt(Ax.composeb, PosInExpr(1::Nil))(1, 1::1::1::Nil) &
                      useAt(Ax.composeb, PosInExpr(1::Nil))(1, 1::1::Nil) &
                      useAt(Ax.composeb, PosInExpr(1::Nil))(1, 1::Nil) &
                      useAt(Ax.composeb, PosInExpr(1::Nil))(1) &
                      DebuggingTactics.print("Close by C2 step lemma") & useLemma(c2step, Some(prop)) &
                      DebuggingTactics.done("Close by C2 induction step")
                    ,
                    DebuggingTactics.print("Proving C2 diff. refine") & cohideR(1) & CMon(1, 1::1::1::1::Nil) &
                      useAt(Ax.DR, PosInExpr(1::Nil))(1) &
                      dW(1) & prop & DebuggingTactics.done("Proving C2 diff. refine")
                  )
                  ,
                  DebuggingTactics.print("Close by C2 use case lemma") & useLemma(c2use, Some(prop)) & DebuggingTactics.done("Close by C2 use case")
                )
              ,
              DebuggingTactics.print("Close by communication guarantee liveness") &
                implyR(1) & ((abstractionb(1) & SaturateTactic(allR(1)))*4) &
                //@todo use communication guarantees of internal ports
                composed(1) & testd(1, 1::Nil) & useAt(Ax.trueAnd)(1, 1::Nil) &
                DebuggingTactics.print("Close by Communication Guarantee Liveness lemma") & useLemma(comGuaranteeLiveness, Some(prop)) & DebuggingTactics.done("Close by communication guarantee liveness")
            )
            ,
            // show
            DebuggingTactics.print("Show InCp") & cohideR(1) &
              CMon(1, 1::1::1::1::1::1::Nil) & implyR(1) & useAt(Ax.diamond, PosInExpr(1::Nil))(-1) & notL(-1) &
              abstractionb(2) & prop & DebuggingTactics.done("Show InCp")
          )
          ) & DebuggingTactics.done("Justify Fout")
    case Some(e) => throw new TacticInapplicableFailure("justifyFout only applicable to implications, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
  })

  /** STTT Fig. 11: Component 1 */
  private def proveSystemCompStep(c1step: Lemma, c2use: Lemma, c2step: Lemma,
                                  compatibility: Lemma, comGuaranteeLiveness: Lemma, fout: Formula) = anon ((pos: Position, seq: Sequent) => {
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

        //@todo support multiple connected ports, support bidirectional communication
        val c2ComGuaranteeLiveness = 
          if (ports(in2).isEmpty) emptyConLiveness
          else comGuaranteeLiveness
        
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
              (anon ((pp: Position, ss: Sequent) => ss.sub(pp) match {
                case Some(have@Box(_, p)) =>
                  useAt(proveBy(Equiv(Box(in1, p), have), chase(1, 0::Nil) & chase(1, 1::Nil) & QE), PosInExpr(1::Nil))(pp)
              }))(pos ++ PosInExpr(1::1::1::1::Nil)) &
              DebuggingTactics.print("Using step lemma") &

              cutAt(Box(plant1, Box(Compose(in1, cp1), inv1)))(1, 1::1::1::Nil) <(
                useAt(Ax.composeb, PosInExpr(1::Nil))(1, 1::1::1::Nil) &
                  useAt(Ax.composeb, PosInExpr(1::Nil))(1, 1::1::Nil) &
                  useAt(Ax.composeb, PosInExpr(1::Nil))(1, 1::Nil) &
                  useAt(Ax.composeb, PosInExpr(1::Nil))(1) &
                  DebuggingTactics.print("Close by C1 step lemma") & useLemma(c1step, Some(prop)) &
                  DebuggingTactics.done("Close by C1 induction step")
                ,
                DebuggingTactics.print("Proving C1 diff. refine") & cohideR(1) & CMon(1, 1::1::1::1::Nil) &
                  composeb(1, 0::1::Nil) & useAt(Ax.DR, PosInExpr(1::Nil))(1) &
                  dW(1) & prop & DebuggingTactics.done("Proving C1 diff. refine")
              ) &
              DebuggingTactics.print("Step done") & DebuggingTactics.done("Step")
            ,
            // show
            justifyFout(fout, plant2Vars, c2ComGuaranteeLiveness, c2use, c2step)('Rlast)
          ) & DebuggingTactics.print("Done disassembling system into components") & DebuggingTactics.done("Disassembling system into components")
      case Some(e) => throw new TacticInapplicableFailure("proveSystemCompStep only applicable to box properties, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
  })

  /** STTT Fig. 10 */
  private def proveSystemStep(c1use: Lemma, c1step: Lemma,
                              c2use: Lemma, c2step: Lemma,
                              pi1Out: Formula, pi2Out: Formula,
                              compatibility: Lemma,
                              comGuaranteeSafety: Lemma, comGuaranteeLiveness: Lemma) = anon ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(Compose(delta3, Compose(ctrl3, Compose(rememberStart@Assign(told, t), Compose(plant3@ODESystem(DifferentialProduct(_, _), q3), Compose(in3, Compose(cp1, Compose(cp2, con))))))), inv3@And(inv1, And(inv2, zeta)))) =>
      //@todo check program shapes in lemmas
      val cr1 :: cr2 :: Nil = (0 to 3) :: (4 to 6) :: Nil
      
      DebuggingTactics.print("Proving component loops and communication guarantees") &
        boxAnd(1) & andR(1) <(
        // inv1
        DebuggingTactics.print("Proving inv1") &
          cr1.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
          proveSystemCompStep(c1step, c2use, c2step, compatibility, comGuaranteeLiveness, Imply(inv2, Box(delta3, Box(ctrl3, Box(rememberStart, Box(plant3, pi2Out))))))(pos) &
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
            useAt(Ax.composeb, PosInExpr(1::Nil))(1, 1::1::1::1::1::1::Nil) &
            useAt(Ax.composeb, PosInExpr(1::Nil))(1, 1::1::1::1::1::Nil) &
            useAt(Ax.composeb, PosInExpr(1::Nil))(1, 1::1::1::1::Nil) &
            DebuggingTactics.print("Done reordering components") &
            proveSystemCompStep(c2step, c1use, c1step, compatibility, comGuaranteeLiveness, Imply(inv1, Box(delta3, Box(ctrl3, Box(rememberStart, Box(plant3, pi1Out))))))(pos) &
            DebuggingTactics.print("Done proving inv2") & DebuggingTactics.done("Proving inv2")
          ,
          // zeta
          DebuggingTactics.print("Proving communication guarantee (zeta step)") &
            cr1.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
            cr2.map(i => PosInExpr(List.fill(i)(1))).map(composeb(1, _)).reduce[BelleExpr](_ & _) &
            (cr1.head to cr2.last).map(i => PosInExpr(List.fill(i)(1))).reverse.map(abstractionb(1, _)).reduce[BelleExpr](_ & _) &
            SaturateTactic(allR(1)) & cohideR(1) & by(comGuaranteeSafety) &
            DebuggingTactics.print("Done proving communication guarantee (zeta step)") &
            DebuggingTactics.done("Proving communication guarantee (zeta step)")
        )
      ) & DebuggingTactics.print("Done proving component loops and communication guarantees") & DebuggingTactics.done("Proving component loops and communication guarantees")
    case Some(e) => throw new TacticInapplicableFailure("proveSystemStep only applicable to box properties, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
  })

  /** STTT Fig. 9 */
  private def proveSystem(systemName: String,
                          c1base: Lemma, c1use: Lemma, c1step: Lemma,
                          c2base: Lemma, c2use: Lemma, c2step: Lemma,
                          compatibility: Lemma,
                          comGuaranteeSafety: Lemma, comGuaranteeLiveness: Lemma) = anon ((pos: Position, seq: Sequent) => seq.sub(pos) match {
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
      implyR(1) & loop(And(inv1, And(inv2, zeta)))(1) & DebuggingTactics.print("Loop") <(
        andR(1) <(
          DebuggingTactics.print("Close by C1 base case lemma") & useLemma(c1base, Some(prop)) & DebuggingTactics.done("C1Base"),
          andR(1) <(
            DebuggingTactics.print("Close by C2 base case lemma") & useLemma(c2base, Some(prop)) & DebuggingTactics.done("C2Base"),
            prop & DebuggingTactics.done("ZetaBase")
          )
        ) & DebuggingTactics.done("Component system base case", Some("user/" + systemName + " Base Case")),
        andR(1) <(
          DebuggingTactics.print("Close by C1 use case lemma") & useLemma(c1use, Some(prop)) & DebuggingTactics.done("C1Use"),
          DebuggingTactics.print("Close by C2 use case lemma") & useLemma(c2use, Some(prop)) & DebuggingTactics.done("C2Use")
        ) & DebuggingTactics.done("Component system use case", Some("user/" + systemName + " Use Case")),
        proveSystemStep(
          c1use, c1step,
          c2use, c2step,
          pi1Out, pi2Out,
          compatibility,
          comGuaranteeSafety, comGuaranteeLiveness)(1) & DebuggingTactics.done("Component system step", Some("user/" + systemName + " Step"))
      )
    case Some(e) => throw new TacticInapplicableFailure("proveSystem only applicable to box properties, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
  })
  
  private val shapeMsg =
    s""""Expected a formula of the shape 
       |   
       |   t=t0 & Om & A1 & A2 
       |   -> 
       |   [{ {portmemory1;portmemory2}; 
       |      {ctrl1;ctrl2}; 
       |      to:=t; 
       |      {t'=1,plant1,plant2};
       |      {in1open;in2open};
       |      {cp1;cp2;con};
       |    }*]((G1&P1) & (G2&P2))
       |  
       |  where Om:    global facts about constant system parameters
       |        A1,A2: assumptions of components
       |        G1,G2: safety guarantees of components
       |        P1,P2: output port guarantees of components
       |        portmemory: remembers the value of input port x in portmemory x0 by x0:=x;
       |        ctrl:       discrete component dynamics
       |        plant:      continuous component dynamics
       |        inXopen:    input ports that remain open in the system
       |        cp:         internal connections of subcomponents
       |        con:        connections between the composed components
       |""".stripMargin

  /** Proves system safety from isolated component and compatibility proofs. */
  @Tactic("proveComponentSystem", codeName = "proveComponentSystem",
    inputs = """System Name:string;;
      C1 Base: Om & A1 -> I1:string;;
      C1 Use:  Om & I1 -> G1 & P1:string;;
      C1 Step: Om & I1 -> [mem1; ctrl1; t0=t; {t'=1,plant1}; in1; cp1;]I1:string;;
      C2 Base: Om & A2 -> I2:string;;
      C2 Use:  Om & I2 -> G2 & P2:string;;
      C2 Step: Om & I2 -> [mem2; ctrl2; t0=t; {t'=1,plant2}; in2; cp2;]I2:string;;
      Compatibility: Om & Z -> [xin:=xo;](Pout(xo) -> Pin(xin)):string;;
      Com Safety:   [xin:=xo;]Z:string;;Com Liveness: <xin:=xo;>true:string""",
    conclusion = "Γ|- t=t0 & Om & A1 & A2 -> [{ {mem1;mem2};{ctrl1;ctrl2};to:=t;{t'=1,plant1,plant2};{in1open;in2open};{cp1;cp2;con};}*]((G1&P1) & (G2&P2)), Δ",
    premises =
      """|- C1 Base: Om & A1 -> I1;;
         |- Om & I1 -> G1 & P1;;
         |- C1 Step: Om & I1 -> [mem1; ctrl1; t0=t; {t'=1,plant1}; in1; cp1;]I1;;
         |- C2 Base: Om & A2 -> I2;;
         |- C2 Use:  Om & I2 -> G2 & P2;;
         |- C2 Step: Om & I2 -> [mem2; ctrl2; t0=t; {t'=1,plant2}; in2; cp2;]I2;;
         |- Compatibility: Om & Z -> [xin:=xo;](Pout(xo) -> Pin(xin));;
         |- Com Safety:   [xin:=xo;]Z;;
         |- Com Liveness: <xin:=xo;>true"""
  )
  def proveSystem(systemName: String,
                  c1baseLemma: String, c1useLemma: String, c1stepLemma: String,
                  c2baseLemma: String, c2useLemma: String, c2stepLemma: String,
                  compatibilityLemma: String,
                  comGuaranteeSafetyLemma: String,
                  comGuaranteeLivenessLemma: String): DependentPositionWithAppliedInputTactic =
    inputanon ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Imply(asys, Box(Loop(prgsys), gsys))) =>
      
      val And(tbootstrap, And(omega, And(a1, a2))) = asys
      val And(And(g1,p1), And(g2,p2)) = gsys
      val Compose(memsys, Compose(ctrlsys, Compose(tmem, Compose(plantsys, Compose(insys, cpsys))))) = prgsys
      
      LemmaDBFactory.lemmaDB.get("user/" + c1baseLemma) match {
        case Some(c1base) => LemmaDBFactory.lemmaDB.get("user/" + c1useLemma) match {
          case Some(c1use) => LemmaDBFactory.lemmaDB.get("user/" + c1stepLemma) match {
            case Some(c1step) => 
              checkComponentLemmas(c1base, c1use, c1step)
              checkSysC1Programs(c1step, prgsys)
              LemmaDBFactory.lemmaDB.get("user/" + c2baseLemma) match {
              case Some(c2base) => LemmaDBFactory.lemmaDB.get("user/" + c2useLemma) match {
                case Some(c2use) => LemmaDBFactory.lemmaDB.get("user/" + c2stepLemma) match {
                  case Some(c2step) =>
                    checkComponentLemmas(c2base, c2use, c2step)
                    checkSysC2Programs(c2step, prgsys)
                    LemmaDBFactory.lemmaDB.get("user/" + compatibilityLemma) match {
                    case Some(compatibility) => LemmaDBFactory.lemmaDB.get("user/" + comGuaranteeSafetyLemma) match {
                      case Some(comSafety) => LemmaDBFactory.lemmaDB.get("user/" + comGuaranteeLivenessLemma) match {
                        case Some(comLiveness) => 
                          proveSystem(systemName, c1base, c1use, c1step, c2base, c2use, c2step,
                            compatibility, comSafety, comLiveness)(pos)
                        case None => throw new InputFormatFailure("Unknown lemma " + comGuaranteeLivenessLemma + "; please prove first")
                      }
                      case None => throw new InputFormatFailure("Unknown lemma " + comGuaranteeSafetyLemma + "; please prove first")
                    }
                    case None => throw new InputFormatFailure("Unknown lemma " + compatibilityLemma + "; please prove first")
                  }
                  case None => throw new InputFormatFailure("Unknown lemma " + c2stepLemma + "; please prove first")
                }
                case None => throw new InputFormatFailure("Unknown lemma " + c2useLemma + "; please prove first")
              }
              case None => throw new InputFormatFailure("Unknown lemma " + c2baseLemma + "; please prove first")
            }
            case None => throw new InputFormatFailure("Unknown lemma " + c1stepLemma + "; please prove first")
          }
          case None => throw new InputFormatFailure("Unknown lemma " + c1useLemma + "; please prove first")
        }
        case None => throw new InputFormatFailure("Unknown lemma " + c1baseLemma + "; please prove first")
      }
    case Some(fml) => throw new TacticInapplicableFailure("Unexpected formula shape.\n" + shapeMsg + "\nBut got " + fml.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position points outside formula")
  })
  
  private def checkComponentLemmas(cbase: Lemma, cuse: Lemma, cstep: Lemma): Unit = {
    val Imply(_, invbase) =
      if (cbase.fact.conclusion.ante.isEmpty) cbase.fact.conclusion.succ.head
      else cbase.fact.conclusion.toFormula
      
    val Imply(invuse, _) =
      if (cuse.fact.conclusion.ante.isEmpty) cuse.fact.conclusion.succ.head
      else cuse.fact.conclusion.toFormula

    val Imply(invstepa, Box(_, invstepb)) =
      if (cstep.fact.conclusion.ante.isEmpty) cuse.fact.conclusion.succ.head
      else cstep.fact.conclusion.toFormula

    if ((FormulaTools.conjuncts(invbase).toSet -- FormulaTools.conjuncts(invuse)).nonEmpty) throw new InputFormatFailure("Component invariants in base case and use case do not match: please provide lemmas A1->I, I -> G1, I->[c]I\n" + invbase.prettyString + " <> " + invuse.prettyString)
    if ((FormulaTools.conjuncts(invstepb).toSet -- FormulaTools.conjuncts(invbase)).nonEmpty) throw new InputFormatFailure("Component invariants in base case and step do not match: please provide lemmas A1->I, I -> G1, I->[c]I\n" + invbase.prettyString + " <> " + invstepa.prettyString)
    if ((FormulaTools.conjuncts(invstepb).toSet -- FormulaTools.conjuncts(invstepa)).nonEmpty) throw new InputFormatFailure("Component invariants in step do not match: please provide lemmas A1->I, I -> G1, I->[c]I\n" + invbase.prettyString + " <> " + invstepa.prettyString)
    
    if (StaticSemantics.freeVars((FormulaTools.conjuncts(invuse).toSet -- FormulaTools.conjuncts(invbase)).
      reduceOption(And).getOrElse(True)).toSet.exists(_.isInstanceOf[Variable])) throw new InputFormatFailure("Component use case makes additional non-global assumptions")
    if (StaticSemantics.freeVars((FormulaTools.conjuncts(invstepa).toSet -- FormulaTools.conjuncts(invbase)).
      reduceOption(And).getOrElse(True)).toSet.exists(_.isInstanceOf[Variable])) throw new InputFormatFailure("Component step makes additional non-global assumptions")
  }
  
  private def checkSysC1Programs(step: Lemma, sys: Program): Unit = {
    val Compose(Compose(mem1,_), Compose(Compose(ctrl1,_), Compose(t1, Compose(plantsys: ODESystem, Compose(Compose(in1,_), Compose(cp1,Compose(_,con))))))) = sys
    val Imply(_, Box(Compose(mem, Compose(ctrl, Compose(t, Compose(plant: ODESystem, Compose(in, cp))))), _)) = step.fact.conclusion.toFormula
    
    checkPrograms(mem1->mem, ctrl1->ctrl, t1->t, plantsys->plant, in1->in, cp1->cp)
  }

  private def checkSysC2Programs(step: Lemma, sys: Program): Unit = {
    val Compose(Compose(_,mem2), Compose(Compose(_,ctrl2), Compose(t2, Compose(plantsys: ODESystem, Compose(Compose(_,in2), Compose(_,Compose(cp2,con))))))) = sys
    val Imply(_, Box(Compose(mem, Compose(ctrl, Compose(t, Compose(plant: ODESystem, Compose(in, cp))))), _)) = step.fact.conclusion.toFormula

    checkPrograms(mem2->mem, ctrl2->ctrl, t2->t, plantsys->plant, in2->in, cp2->cp)
  }

  private def checkPrograms(mem: (Program, Program), 
                            ctrl: (Program, Program),
                            t: (Program, Program),
                            plant: (ODESystem, ODESystem),
                            in: (Program, Program),
                            cp: (Program, Program)): Unit = {
    if (mem._1 != mem._2) throw new InputFormatFailure("System and component port memories must agree, but " + mem._1 + " <> " + mem._2)
    if (ctrl._1 != ctrl._2) throw new InputFormatFailure("System and component controllers must agree, but " + ctrl._1 + " <> " + ctrl._2)
    if (t._1 != t._2) throw new InputFormatFailure("System and component time memory must agree, but " + t._1 + " <> " + t._2)
    if (!DifferentialHelper.atomicOdes(plant._2).toSet.subsetOf(DifferentialHelper.atomicOdes(plant._1).toSet)) throw new InputFormatFailure("System plant must contain component plant, but " + plant._1.prettyString + " does not contain all of " + plant._2)
    if (!ports(in._1).toSet.subsetOf(ports(in._2).toSet)) throw new InputFormatFailure("System input ports must be subset of component input ports, but " +
      ports(in._1).map(p => p._1.prettyString + " (" + p._2.prettyString + ")").mkString(",") + " not subset of " +
      ports(in._2).map(p => p._1.prettyString + " (" + p._2.prettyString + ")").mkString(","))
    if (cp._1 != cp._2) throw new InputFormatFailure("System and component internal connections must agree, but " + cp._1 + " <> " + cp._2)
    //@todo check that connections cover remaining (non-open) input ports
  }
}
