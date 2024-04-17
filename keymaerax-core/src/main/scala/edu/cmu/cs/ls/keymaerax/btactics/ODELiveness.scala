/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.btactics.ODEInvariance._
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics.implyRi
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3.ineqNormalize
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.btactics.macros.{
  DisplayLevelAll,
  DisplayLevelBrowse,
  DisplayLevelInternal,
  ProvableInfo,
  Tactic,
}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.DependencyAnalysis._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.parser.Declaration
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.tools.ext.Mathematica

import scala.collection.immutable
import scala.collection.mutable.ListBuffer
import scala.reflect.runtime.universe

/**
 * Implements ODE tactics for liveness.
 *
 * Created by yongkiat on 24 Feb 2020.
 */

object ODELiveness extends TacticProvider {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) = (ODELiveness.getClass, universe.typeOf[ODELiveness.type])

  private val namespace = "odeliveness"

  /**
   * Computes the affine form for ODEs
   * @todo:
   *   this may also be extended to work with domain constraints
   * @param odes
   *   the ODEs to put into affine form
   * @return
   *   A (matrix of terms), b (list of terms), x (list of variables) such that x'=Ax+b
   */
  def affine_form(odes: DifferentialProgram): (List[List[Term]], List[Term], List[Term]) = {

    val odels = DifferentialProduct
      .listify(odes)
      .map {
        case AtomicODE(x, e) => (x, e)
        case _ => ??? // probably error
      }

    val lhs = odels.map(_._1) // list of LHS y' of the ODEs
    val lhsvar = lhs.map(_.x.asInstanceOf[BaseVariable]) // list of y corresponding to the y'
    val rhs = odels.map(_._2) // list of RHS g(x,y) corresponding to the y'

    val toolCheck = ToolProvider.simplifierTool()

    val tool = toolCheck match {
      case None => None
      // @todo: this throws away the Z3 simplifier because it fails too much
      case Some(t) => { if (t.isInstanceOf[Mathematica]) Some(t) else None }
    }

    // the system matrix "A"
    val amat = rhs.map(t => simplifiedJacobian(t, lhsvar, tool))

    // ensure that "A" is actually linear
    val amatfree = amat.flatten.map(t => StaticSemantics.freeVars(t))
    if (amatfree.exists(s => lhsvar.exists(v => s.contains(v)))) {
      throw new IllegalArgumentException(
        "Unable to automatically place ODE into affine form. Detected system matrix: " + amat
      )
    }

    // Extracts the "affine part" by replacing all the LHS with 0 and then simplifying
    val rep0 = { e: Term => if (lhsvar.contains(e)) Some(Number(0): Term) else None }
    val rhssub = rhs.map(SubstitutionHelper.replacesFree(_)(rep0).asInstanceOf[Term])

    val bvec = rhssub.map(simpWithTool(tool, _))

    (amat, bvec, lhsvar)
  }

  // Versions of scalar DG that drop quantifiers for ease of substitution
  // todo: these should probably be the core statement of the axiom rather than splitting into two each time.
  private lazy val dgb = remember(
    "[{c{|y_|}&q(|y_|)}]p(|y_|) <-> [{c{|y_|},y_'=a(|y_|)*y_+b(|y_|)&q(|y_|)}]p(|y_|)".asFormula,
    equivR(1) < (
      useAt(Ax.DGpp, PosInExpr(0 :: Nil))(-1) &
        useAt(Ax.commaCommute)(-1, 0 :: Nil) & implyRi &
        byUS(Ax.ally),
      useAt(Ax.DGa, PosInExpr(0 :: Nil))(1) &
        useAt(Ax.existsey, PosInExpr(1 :: Nil))(1) & id
    ),
    namespace,
  )

  private lazy val dgd = remember(
    "<{c{|y_|}&q(|y_|)}>p(|y_|) <-> <{c{|y_|},y_'=a(|y_|)*y_+b(|y_|)&q(|y_|)}>p(|y_|)".asFormula,
    equivR(1) < (
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(1) &
        useAt(Ax.diamond, PosInExpr(1 :: Nil))(-1) & prop & implyRi & equivifyR(1) & commuteEquivR(1) & byUS(dgb),
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(1) &
        useAt(Ax.diamond, PosInExpr(1 :: Nil))(-1) & prop & implyRi & equivifyR(1) & byUS(dgb)
    ),
    namespace,
  )

  private lazy val getDDGhelperLemma = remember(
    "[a_{|^@|};]d(||)=a(||)*z(||)+b(||) -> [a_{|^@|};]c(||) <= a(||)*f(||)+b(||) -> [a_{|^@|};]d(||)-c(||)>=a(||)*(z(||)-f(||))"
      .asFormula,
    implyR(1) & implyR(1) & andLi & useAt(Ax.boxAnd, PosInExpr(1 :: Nil))(-1) &
      monb & andL(-1) & implyRi()(AntePosition(2), SuccPosition(1)) & implyRi &
      byUS(proveBy("d()=a()*z()+b()->c()<=a()*f()+b()->d()-c()>=a()*(z()-f())".asFormula, QE)),
    namespace,
  )

  // Turns a raw vectorial (bounded) DG instance into a raw DDG instance
  def getDDG(dim: Int): ProvableSig = {

    // Note: because we need to "free up" one ghost variable, this duplicates a lot of core functionality
    val ghostvar = BaseVariable("z_")

    // Also need to "free up" the ghost variable used by dbx internally..
    val dbxghostvar = BaseVariable("y_")

    // The list of variables y__1, y__2, ..., y__dim
    val ghosts = (1 to dim).map(i => BaseVariable("y_", Some(i)))
    // The list of RHS g1(||), g2(||), ..., gdim(||)
    // @todo: UnitFunctionals may need an index argument
    val ghostRHSs = (1 to dim).map(i => UnitFunctional("g" + i, Except(dbxghostvar :: ghostvar :: Nil), Real))
    // The list ghost ODEs y__1'=g1(||), y__2'=g2(||), ..., y__dim'=gdim(||)
    val ghostODEList = (ghosts zip ghostRHSs).map { case (y, rhs) => AtomicODE(DifferentialSymbol(y), rhs) }
    // The list of ghost ODEs as a single ODE
    val ghostODEs = ghostODEList.reduce(DifferentialProduct.apply)

    // The base ODE c{|y_|}
    val baseODE = DifferentialProgramConst("c", Except(dbxghostvar +: ghostvar +: ghosts))
    // The base ODE extended with ghost ODEs
    val extODE = DifferentialProduct(ghostODEs, baseODE)
    val domain = UnitPredicational("q", Except(dbxghostvar +: ghostvar +: ghosts))
    val post = UnitPredicational("p", Except(dbxghostvar +: ghostvar +: ghosts))

    // The squared norm of the vector ||y__1, y__2, ..., y__dim||^2
    val sqnorm = ghosts.tail.foldLeft(Times(ghosts.head, ghosts.head): Term)((f, e) => Plus(f, Times(e, e)))
    val cofA = UnitFunctional("a_", Except(dbxghostvar +: ghostvar +: ghosts), Real)
    val cofB = UnitFunctional("b_", Except(dbxghostvar +: ghostvar +: ghosts), Real)
    val cofF = UnitFunctional("f_", Except(ghosts), Real)
    // The norm bound required of the ghost ODEs (||y_||^2)' <= a(|y_|)||y_||^2 + b(|y_|)
    val normBound = LessEqual(Differential(sqnorm), Plus(Times(cofA, sqnorm), cofB))

    val DDGimply = Imply(
      // [{c{|y_|},y_'=g(||)&q(|y_|)}] (||y_||^2)' <= f(|y_|) ->
      Box(ODESystem(extODE, domain), normBound),
      // [{c{|y_|},y_'=g(||)&q(|y_|)}]p(|y_|) -> [{c{|y_|}&q(|y_|)}]p(|y_|)
      Imply(Box(ODESystem(extODE, domain), post), Box(ODESystem(baseODE, domain), post)),
    )

    val unifA = UnificationMatch.unifiable("a(|z_|) + b(|z_|)".asTerm, Plus(cofA, cofB)).get.usubst
    // The extra urename frees up y_
    val dgbU = dgb.fact(URename(dbxghostvar, ghostvar, semantic = true))(unifA)

    val vdgrawimply = ElidingProvable(Provable.vectorialDG(dim)._1, Declaration(Map.empty))
    val unifB = UnificationMatch.unifiable(cofF, ghostvar).get.usubst
    val vdg = vdgrawimply(unifB)
    // Turn c{|y_1,...y_n|} into c{|y_1,...,y_n|}

    // y > ||y_||^2 greater makes it easier to use with dbxgt
    val inv = Greater(Minus(ghostvar, sqnorm), Number(0))

    // g(|y_|) is the cofactor from darbouxGt
    val unifC = UnificationMatch.unifiable("g(|y_|)".asTerm, cofA).get.usubst
    val dbx = Ax.DBXgt.provable(unifC)

    val unifD = UnificationMatch.unifiable("c".asDifferentialProgram, extODE).get.usubst
    val commute = ElidingProvable(Provable.axioms(", commute")(unifD), Declaration(Map.empty))

    // TODO: change to "remember" when parsing is supported
    val pr = proveBy(
      Imply(inv, DDGimply),
      implyR(1) &
        implyR(1) &
        useAt(dgbU)(-2) &
        useAt(dgbU)(1, 0 :: Nil) &
        useAt(dgbU)(1, 1 :: Nil) &
        useAt(vdg, PosInExpr(1 :: Nil))(1) &
        generalize(inv)(1) < (
          implyRi & useAt(dbx, PosInExpr(1 :: Nil))(1) &
            useAt(Ax.Dminus)(1, 1 :: 0 :: Nil) &
            implyRi &
            useAt(getDDGhelperLemma, PosInExpr(1 :: Nil))(1) &
            useAt(Ax.DvarAxiom)(1, 1 :: 0 :: Nil) &
            useAt(commute, PosInExpr(0 :: Nil))(1) &
            useAt(ElidingProvable(
              Provable.axioms("DE differential effect (system)")(URename("x_".asVariable, ghostvar, semantic = true)),
              Declaration(Map.empty),
            ))(1) &
            G(1) & DassignbCustom(1) &
            byUS(Ax.equalReflexive),
          QE
        ),
    )
    // , namespace).fact

    val pr2 = proveBy(
      DDGimply,
      cut(Exists(ghostvar :: Nil, inv)) < (
        skip,
        cohideR(2) & QE
      ),
    )

    // existsL does something crazy, so explicitly call Skolemize instead
    val pr3 = proveBy(pr2(Skolemize(AntePos(0)), 0), implyRi & byUS(pr))

    pr3
  }

  /**
   * Helper that gets the appropriate VDG instance (already instantiated for the ghosts and ODE by renaming and friends)
   *
   * @param ghostODEs
   *   the ghost ODEs
   * @return
   *   both directions of VDG instantiated for the ghost ODEs (everything else is left uninstantiated)
   */
  def getVDGinst(ghostODEs: DifferentialProgram): (ProvableSig, ProvableSig) = {

    val odels = DifferentialProduct
      .listify(ghostODEs)
      .map {
        case AtomicODE(x, e) => (x, e)
        case _ => throw new IllegalArgumentException("list of ghost ODEs should all be atomic, found: " + ghostODEs)
      }
    val ghostlist = DifferentialProduct.listify(ghostODEs)
    val dim = ghostlist.length
    val (vdgrawimply, vdgrawylpmi) = Provable.vectorialDG(dim)

    // @TODO: this very manually applies the uniform renaming part, since it's not automated elsewhere yet (?)
    // would also be much cleaner if one could access the renaming part more easily.
    val ghosts = (1 to dim).map(i => BaseVariable("y_", Some(i)))
    val lhs = odels.map(_._1.x) // variables in the ODE
    val vdgimplyren = (lhs zip ghosts).foldLeft(vdgrawimply)((acc, bv) => acc(URename(bv._1, bv._2, semantic = true)))
    val vdgylpmiren = (lhs zip ghosts).foldLeft(vdgrawylpmi)((acc, bv) => acc(URename(bv._1, bv._2, semantic = true)))

    // Now do the substitution part
    val odeimplyren = vdgimplyren.conclusion.succ(0).sub(PosInExpr(0 :: 0 :: 0 :: Nil)).get
    val unif = UnificationMatch
      .unifiable(odeimplyren, DifferentialProduct(ghostODEs, DifferentialProgramConst("c", Except(lhs))))
      .get

    val resimply = vdgimplyren(unif.usubst)
    val resylpmi = vdgylpmiren(unif.usubst)

    (ElidingProvable(resimply, Declaration(Map.empty)), ElidingProvable(resylpmi, Declaration(Map.empty)))
  }

  /**
   * Helper that gets the appropriate DDG instance (already instantiated for the ghosts by renaming and friends) This
   * helps simplify the (y^2)' term away
   *
   * @param ghostODEs
   *   the ghosts to add to the ODE
   * @return
   *   DDG instantiated for the particular boxode question
   */
  def getDDGinst(ghostODEs: DifferentialProgram): ProvableSig = {

    val odels = DifferentialProduct
      .listify(ghostODEs)
      .map {
        case AtomicODE(x, e) => (x, e)
        case _ => throw new IllegalArgumentException("list of ghost ODEs should all be atomic, found: " + ghostODEs)
      }
    val ghostlist = DifferentialProduct.listify(ghostODEs)
    val dim = ghostlist.length
    val ddgraw = getDDG(dim)

    // @TODO: this very manually applies the uniform renaming part, since it's not automated elsewhere yet (?)
    // would also be much cleaner if one could access the renaming part more easily.
    val ghosts = (1 to dim).map(i => BaseVariable("y_", Some(i)))
    val lhs = odels.map(_._1.x) // variables in the ODE
    val ddgren = (lhs zip ghosts).foldLeft(ddgraw)((acc, bv) => acc(URename(bv._1, bv._2, semantic = true)))

    // Now do the substitution part
    val oderen = ddgren.conclusion.succ(0).sub(PosInExpr(1 :: 0 :: 0 :: 0 :: Nil)).get
    val boxren = ddgren.conclusion.succ(0).sub(PosInExpr(1 :: 1 :: 1 :: Nil)).get
    val unif = UnificationMatch
      .unifiable(
        oderen,
        DifferentialProduct(ghostODEs, DifferentialProgramConst("c", Except("y_".asVariable +: "z_".asVariable +: lhs))),
      )
      .get
      .usubst

    val res = ddgren(unif)

    // (||y||^2)' = 2y.g(x,yy)
    val bnd = Times(Number(2), odels.map(ve => Times(ve._1.x, ve._2)).reduce(Plus.apply))

    val concl = res.conclusion.succ(0).sub(PosInExpr(1 :: Nil)).get.asInstanceOf[Formula]
    val pre = res.conclusion.succ(0).sub(PosInExpr(0 :: Nil)).get.asInstanceOf[Formula]

    simplifyPre(res, bnd, dim)
  }

  // helper that simplifies the precondition of ddg
  private def simplifyPre(pr: ProvableSig, bnd: Term, length: Int): ProvableSig = {
    val seq = pr.conclusion
    val left = seq.succ(0).sub(PosInExpr(0 :: Nil)).get.asInstanceOf[Formula]
    val right = seq.succ(0).sub(PosInExpr(1 :: Nil)).get.asInstanceOf[Formula]

    val leftnew = left.replaceAt(PosInExpr(1 :: 0 :: Nil), bnd)

    proveBy(
      Imply(leftnew, right),
      implyR(1) & cutR(left)(1) < (
        implyRi & useAt(ineqLem, PosInExpr(1 :: Nil))(1) &
          DifferentialTactics.Dconstify(
            derive(1, PosInExpr(1 :: 1 :: Nil)) &
              (DESystemCustom(1) * length) & G(1) & DassignbCustom(1) & QE
          )(1),
        cohideR(1) & by(pr)
      ),
    )
  }

  /** Single use of DE system */
  // todo: copied and tweaked from DifferentialTactics
  // was "DE system step"
  private lazy val DESystemCustom: DependentPositionTactic = anon((pos: Position, sequent: Sequent) =>
    sequent.sub(pos) match {
      case Some(f @ Box(ODESystem(DifferentialProduct(AtomicODE(xp @ DifferentialSymbol(x), t), c), h), p)) =>
        val ax = Provable.axioms("DE differential effect (system)")(URename("x_".asVariable, x, semantic = true))
        useAt(ElidingProvable(ax, Declaration(Map.empty)), PosInExpr(0 :: Nil))(pos)
      case _ => skip
    }
  )

  /** Repeated use of Dassignb */
  // todo: copied and tweaked from DifferentialTactics
  // was "DE system step"
  private lazy val DassignbCustom: DependentPositionTactic = anon((pos: Position, sequent: Sequent) =>
    sequent.sub(pos) match {
      case Some(Box(Assign(xp @ DifferentialSymbol(x), f0), p)) =>
        val ax = Provable.axioms("[':=] differential assign")(URename("x_".asVariable, x, semantic = true))
        useAt(ElidingProvable(ax, Declaration(Map.empty)), PosInExpr(0 :: Nil))(pos) & DassignbCustom(pos)
      case _ => skip
    }
  )

  // returns the diff ghost instantiated and discharged
  private def affineVDGprecond(ghostODEs: DifferentialProgram, boxode: Formula = True): ProvableSig = {

    // @note: throws IllegalArgumentException if affine form fails
    val (a, b, x) = affine_form(ghostODEs)

    // val ghosts = DifferentialProduct.listify(ghostODEs)
    val boundLem = ODEInvariance.affine_norm_bound(b.length)

    // the LHS 2*((A.x).x) + 2*(b.x)
    val lhs = boundLem.conclusion.succ(0).sub(PosInExpr(0 :: Nil)).get

    val lhsInst = Plus(Times(Number(2), dot_prod(matvec_prod(a, x), x)), Times(Number(2), dot_prod(b, x)))

    // Note: this should always unify
    val unif = UnificationMatch.unifiable(lhs, lhsInst).get.usubst
    val bound = boundLem(unif)

    // obtain the Lipschitz bounds by unification
    val lipsL = bound.conclusion.succ(0).sub(PosInExpr(1 :: 0 :: 0 :: Nil)).get
    // lipsM should always be 1 thanks to the way affine_norm_bound is proved
    val lipsM = bound.conclusion.succ(0).sub(PosInExpr(1 :: 1 :: Nil)).get

    val ddgpre = getDDGinst(ghostODEs)

    val lipsLsub = ddgpre.conclusion.succ(0).sub(PosInExpr(0 :: 1 :: 1 :: 0 :: 0 :: Nil)).get
    val lipsMsub = ddgpre.conclusion.succ(0).sub(PosInExpr(0 :: 1 :: 1 :: 1 :: Nil)).get

    val lipsLunif = UnificationMatch.unifiable(lipsLsub, lipsL).get.usubst
    val lipsMunif = UnificationMatch.unifiable(lipsMsub, lipsM).get.usubst
    val ddg = (ddgpre(lipsLunif))(lipsMunif)

    val goal = ddg.conclusion.succ(0).sub(PosInExpr(1 :: Nil)).get.asInstanceOf[Formula]
    val pre = ddg.conclusion.succ(0).sub(PosInExpr(0 :: Nil)).get.asInstanceOf[Formula]

    val pr = proveBy(
      goal,
      cutR(pre)(1)
        < (
          G(1) & cutR(bound.conclusion.succ(0))(1) < (
            by(bound),
            useAt(ineqLem1, PosInExpr(1 :: Nil))(1) & QE
          ),
          by(ddg)
        ),
    )

    pr
  }

  private lazy val ineqLem1 = remember("f_()=g_() -> f_()<=h_() ->  g_()<=h_()".asFormula, QE, namespace)
  private lazy val ineqLem = remember(
    "[a_{|^@|};]f(||)=g(||) -> [a_{|^@|};]f(||) <= h(||) -> [a_{|^@|};]g(||)<=h(||)".asFormula,
    implyR(1) & implyR(1) & andLi & useAt(Ax.boxAnd, PosInExpr(1 :: Nil))(-1) & monb & andL(-1) & implyRi()(
      AntePosition(2),
      SuccPosition(1),
    ) & implyRi & byUS(ineqLem1),
    namespace,
  )

  /**
   * Given ODE, returns the global existence axiom `<t'=1,x'=f(x)>t>p()` (if it proves)
   * @param ode
   * @return
   *   (optional) ProvableSig proving the global existence axiom, None if failed
   */
  def deriveGlobalExistence(ode: DifferentialProgram): Option[ProvableSig] = {

    val timevar = "gextimevar_".asVariable
    val rhs = "p()".asTerm
    val post = Greater(timevar, rhs)
    val timeode = "gextimevar_'=1".asDifferentialProgram

    val odels = DifferentialProduct
      .listify(ode)
      .map {
        case ve @ AtomicODE(x, e) => (x.x, ve)
        case _ => return None
      }
      .toMap

    val adjs = analyseODEVars(ODESystem(ode, True), ignoreTest = true, checkLinear = false)

    val ls = scc(adjs).map(_.toList)

    val odeGroups = ls.map(vs => {
      val odes = vs.map(vv => odels(vv))
      odes.tail.foldLeft(odes.head: DifferentialProgram)((p, r) => DifferentialProduct(p, r))
    })

    var pr = Ax.TExgt.provable // Ax.TExge for the >= version
    var curode = timeode

    for (odeG <- odeGroups) {

      curode = DifferentialProduct(odeG, curode)

      val vdg =
        try affineVDGprecond(odeG)
        catch { case e: IllegalArgumentException => return None }

      val vdgflip = flipModality(vdg)
      pr = useFor(vdgflip, PosInExpr(0 :: Nil))(Position(1))(pr)
    }

    val resode = DifferentialProduct(timeode, ode)
    val goal = ls.reverse.flatMap(_.toList)
    val sortTac = AxiomaticODESolver.selectionSort(True, Not(post), resode, goal :+ timevar, AntePosition(1))

    val res = proveBy(
      Diamond(ODESystem(resode, True), post),
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(1) & notR(1) & sortTac &
        useAt(Ax.box, PosInExpr(1 :: Nil))(-1) & notL(-1) &
        useAt(Ax.doubleNegation)(1, 1 :: Nil) & byUS(pr),
    )

    Some(res)
  }

  // Helper to remove a nonlinear univariate ODE.
  // This is a bit different from the others in that it needs to inspect the current sequent in order to
  // correctly remove the univariate ODE. Thus, it throws BelleThrowables for errors
  private def removeODEUnivariate(ode: List[DifferentialProgram], cont: BelleExpr): DependentPositionTactic =
    anon((pos: Position, seq: Sequent) => {

      val (sys, post) = seq.sub(pos) match {
        case Some(Box(sys: ODESystem, post)) => (sys, post)
        case Some(e) => throw new TacticInapplicableFailure(
            "removeODEUnivariate only applicable to box ODEs, but got " + e.prettyString
          )
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      if (!ode.head.isInstanceOf[AtomicODE])
        throw new TacticInapplicableFailure("removeODEUnivariate only applies to univariate ODE")

      val uode = ode.head.asInstanceOf[AtomicODE]

      val x = uode.xp.x
      val rhs = uode.e

      val deps = StaticSemantics.freeVars(rhs).-(x).intersect(StaticSemantics.boundVars(sys))

      if (!deps.isEmpty)
        // This is not a proper univariate case, forward to the nonlinear tactic instead
        throw new TacticInapplicableFailure(
          "removeODEUnivariate only applies to univariate ODE (independent of subsequent ODEs). Found incorrect dependencies on variables: " + deps
        )

      val deg = ToolTactics.varDegree(rhs, x)
      val coeff1 = (1 to (deg - 1)).map(i => Variable("coeff", Some(i)))
      val tmls = coeff1.zipWithIndex.map(bi => Times(bi._1, Power(x, Number(bi._2 + 1))))
      val tm = tmls.foldLeft(Variable("coeff", Some(0)): Term)((e, b) => Plus(e, b))
      val coeffs = Variable("coeff", Some(0)) +: coeff1

      val rootvar = Variable("root_")
      val oldvar = Variable("initx_")
      val rootrhs = rhs.replaceFree(x, rootvar)
      val zero = Number(0)

      // Set up the precondition
      val req = Equal(rootrhs, zero) // r' = 0
      val disj0 = Equal(Minus(x, rootvar), zero) // v-r = 0
      val pleq = LessEqual(Minus(x, rootvar), zero) // v-r <= 0
      val disj1 = And(pleq, Greater(rhs, zero)) // v-r <= 0 & rhs > 0
      val pgeq = GreaterEqual(Minus(x, rootvar), zero) // v-r >= 0
      val disj2 = And(pgeq, Less(rhs, zero)) // v-r >= 0 & rhs < 0

      val precond: Formula = Exists(rootvar :: Nil, And(req, Or(disj0, Or(disj1, disj2))))
      val starter = proveBy(Sequent(seq.ante, seq.succ :+ precond), ToolTactics.hideNonFOL & QE)

      if (!starter.isProved) {
        throw new TacticInapplicableFailure("Initial conditions insufficient for global existence on variable: " + x)
      }

      // Forcing darboux format
      val inv = Equal(rhs, Times(Minus(x, rootvar), tm))
      val dbxforce = coeffs.foldLeft(Forall(x :: Nil, inv): Formula)((v, e) => Exists(e :: Nil, v))

      // The main tactic that discharges the splitting
      val splittac = orL(-3) < (
        // v=r case
        dC(disj0)(1) < (
          DifferentialTactics.diffWeakenG(1) & QE, // could be done manually with US instead of QE
          dRI(1)
        ) // maybe can be made faster
        ,
        orL(-3) < (
          andL(-3) &
            DifferentialTactics.DconstV(1) & dC(pleq)(1) < (
              dC(GreaterEqual(x, oldvar))(1) < (
                DifferentialTactics.diffWeakenG(1) & QE, DifferentialTactics.dgBarrier(1)
              ),
              ODEInvariance.sAIclosed(1)
            ),
          andL(-3) &
            DifferentialTactics.DconstV(1) & dC(pgeq)(1) < (
              dC(LessEqual(x, oldvar))(1) < (DifferentialTactics.diffWeakenG(1) & QE, DifferentialTactics.dgBarrier(1)),
              ODEInvariance.sAIclosed(1)
            )
        )
      )

      val tac = cut(precond) < (
        existsL(Symbol("Llast")) &
          cut(Exists(oldvar :: Nil, Equal(x, oldvar))) < (
            existsL(Symbol("Llast")) & exhaustiveEqL2R(Symbol("Llast")), cohideR(Symbol("Rlast")) & QE
          ) &
          andL(-(seq.ante.length + 1)) &
          cut(Box(sys, LessEqual(Times(x, x), Plus(Times(oldvar, oldvar), Times(rootvar, rootvar))))) < (
            (hideL(-(seq.ante.length + 1)) * 3) & removeODENonLin(
              uode,
              true,
              hideL(-(seq.ante.length + 1)) & cont,
              LessEqual(Times(x, x), Plus(Times(oldvar, oldvar), Times(rootvar, rootvar))),
            )(pos),
            // From here, we don't need any extra information
            (hideL(-1) * seq.ante.length) &
              cohideOnlyR(Symbol("Rlast")) & splittac
          ),
        by(starter)
      )

      tac
    })

  // same as hideNonFOL but only does the antecedents
  private def hideNonFOLLeft: DependentTactic = anon((sequent: Sequent) =>
    (sequent
      .ante
      .zipWithIndex
      .filter({ case (fml, _) => !fml.isFOL })
      .reverse
      .map({ case (fml, i) => hideL(AntePos(i), fml) })).reduceOption[BelleExpr](_ & _).getOrElse(skip)
  )

  // Helper to remove a nonlinear ODE
  private def removeODENonLin(
      ode: DifferentialProgram,
      strict: Boolean,
      cont: BelleExpr,
      hint: Formula,
  ): DependentPositionTactic = anon((pos: Position, seq: Sequent) => {

    // The hints are constrained to be exactly one of two forms
    val vdgpre = getVDGinst(ode)._1
    val vdgsubst = UnificationMatch(vdgpre.conclusion.succ(0).sub(PosInExpr(1 :: 0 :: Nil)).get, seq.sub(pos).get)
      .usubst
    // the concrete vdg instance
    val vdg = vdgpre(vdgsubst)
    val vdgasm = vdg.conclusion.succ(0).sub(PosInExpr(0 :: 1 :: Nil)).get

    val ddgpre = getDDGinst(ode)
    val ddgsubst = UnificationMatch(ddgpre.conclusion.succ(0).sub(PosInExpr(1 :: 0 :: Nil)).get, seq.sub(pos).get)
      .usubst
    // the concrete ddg instance
    val ddg = ddgpre(ddgsubst)
    val ddgasm = ddg.conclusion.succ(0).sub(PosInExpr(0 :: 1 :: Nil)).get

    val finalrwopt = UnificationMatch.unifiable(vdgasm, hint) match {
      case Some(res) => Some(vdg(res.usubst))
      case None => UnificationMatch.unifiable(ddgasm, hint) match {
          case Some(res) => Some(ddg(res.usubst))
          case None => {
            if (strict) throw new TacticInapplicableFailure(
              "odeReduce failed to autoremove: " + ode +
                ". Try to add a hint of either this form: " + vdgasm +
                " or this form: " + ddgasm
            )
            else None
          }
        }
    }

    finalrwopt match {
      case Some(finalrw) => {
        val concl = finalrw.conclusion.succ(0).sub(PosInExpr(1 :: 1 :: Nil)).get.asInstanceOf[Formula]

        cutL(concl)(pos) < (
          cont,
          cohideOnlyR(Symbol("Rlast")) &
            useAt(finalrw, PosInExpr(1 :: Nil))(1) &
            odeUnify(1) &
            hideNonFOLLeft &
            ODE(1) & done
        )
      }
      case None => skip
    }
  })

  private def removeODEs(
      ls: List[DifferentialProgram],
      pos: Position,
      strict: Boolean,
      hints: List[Formula],
  ): BelleExpr = {

    if (ls.isEmpty) return skip

    val vdg =
      try affineVDGprecond(ls.head)
      catch {
        case e: IllegalArgumentException => {
          // The hint to use when using removeODENonLin
          val (hint, rest) = if (hints.isEmpty) (LessEqual(Number(0), Number(0)), Nil) else (hints.head, hints.tail)
          // If it is a univariate ODE just remove it, otherwise fallback to nonlinear
          return (removeODEUnivariate(ls, removeODEs(ls.tail, pos, strict, hints))(pos) |
            removeODENonLin(ls.head, strict, removeODEs(ls.tail, pos, strict, rest), hint)(pos))
        }
      }

    useAt(vdg, PosInExpr(0 :: Nil))(pos) & removeODEs(ls.tail, pos, strict, hints)
  }

  /**
   * Applied to a top-level position containing a succedent diamond, this tactic removes irrelevant ODEs
   *
   * @param strict
   *   whether to throw an error when it meets a nonlinear ODE that can't be reduced
   * @param hints
   *   a list of
   * @return
   *   reduces away all irrelevant ODEs
   */
  def odeReduce(strict: Boolean = true, hints: List[Formula]): DependentPositionTactic =
    anon((pos: Position, seq: Sequent) => {
      if (!(pos.isTopLevel && pos.isSucc))
        throw new IllFormedTacticApplicationException("odeReduce is only applicable at a top-level succedent")

      val (sys, post) = seq.sub(pos) match {
        case Some(Diamond(sys: ODESystem, post)) => (sys, post)
        case Some(e) =>
          throw new TacticInapplicableFailure("odeReduce only applicable to diamond ODEs, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      val ode = sys.ode

      // ODEs in order of appearance
      val odels = DifferentialProduct
        .listify(ode)
        .map {
          case ve @ AtomicODE(x, e) => (x.x, ve)
          case _ => throw new TacticInapplicableFailure("odeReduce only applicable to concrete ODEs")
        }
        .toMap

      // The set of variables transitively depended on by the postcondition and domain constraint
      // These cannot be removed!
      val fvs = StaticSemantics.freeVars(And(sys.constraint, post)).toSet
      val basefvs = fvs.filter(v => v.isInstanceOf[BaseVariable]).map(v => v.asInstanceOf[BaseVariable])
      val unremovable = analyseODE(ODESystem(ode, True), basefvs, ignoreTest = true, checkLinear = false)._1.toList

      val adjs = analyseODEVars(ODESystem(ode, True), ignoreTest = true, checkLinear = false)

      // The remaining removable ODEs
      val ls = scc(adjs).map(_.toList)

      if (ls.length <= 1)
        // unable to do anything for a single group of ODE
        skip
      else {
        val lsr = ls.filter(vs => vs.intersect(unremovable).isEmpty)
        val lsu = ls.filter(vs => vs.intersect(unremovable).nonEmpty)

        // println(ls)

        // We will remove the ODEs in ls from back to front
        val odeGroups = lsr.map(vs => {
          val odes = vs.map(vv => odels(vv))
          odes.tail.foldLeft(odes.head: DifferentialProgram)((p, r) => DifferentialProduct(p, r))
        })

        val goal = lsr.reverse.flatMap(_.toList) ++ lsu.flatMap(_.toList)
        val sortTac =
          AxiomaticODESolver.selectionSort(sys.constraint, Not(post), ode, goal, AntePosition(seq.ante.length + 1))

        val red = removeODEs(odeGroups.reverse, AntePosition(seq.ante.length + 1), strict, hints)
        //    val resode = DifferentialProduct(timeode,ode)
        //    val goal = ls.reverse.flatMap(_.toList)
        //    val sortTac = AxiomaticODESolver.selectionSort(True, Not(post), resode, goal:+timevar, AntePosition(1))

        // Moves diamonds into anteposition and sorts
        useAt(Ax.diamond, PosInExpr(1 :: Nil))(pos) & notR(pos) & sortTac &
          // Apply the reduction
          red &
          // Moves back into diamond
          useAt(Ax.box, PosInExpr(1 :: Nil))(AntePosition(seq.ante.length + 1)) & notL(Symbol("Llast")) &
          useAt(Ax.doubleNegation)(seq.succ.length, 1 :: Nil) &
          SequentCalculus.exchangeR(Position(seq.succ.length), pos)
      }
    })

  // Tries to make the second ODE line up with the first one by deleting and reordering ODEs
  // dom is the domain of the second ODE and post is the postcond of the first
  private def compatODE(
      ode1: DifferentialProgram,
      ode2: DifferentialProgram,
      dom: Formula,
      post: Formula,
  ): Option[BelleExpr] = {
    val ode1ls = DifferentialProduct.listify(ode1)
    val ode2ls = DifferentialProduct.listify(ode2)

    // Common case: both ODEs are the same
    if (ode1ls == ode2ls) { Some(skip) }
    // ODE1 must be a subset of ODE2
    else if (ode1ls.diff(ode2ls).nonEmpty) None
    else {
      // Ignore non atomic ODEs
      if (!ode1ls.forall(_.isInstanceOf[AtomicODE]) && !ode2ls.forall(_.isInstanceOf[AtomicODE])) return None
      // ODE2 can have some extras, which we can get rid of
      val extra = ode2ls.diff(ode1ls)

      val extravars = extra.map(_.asInstanceOf[AtomicODE].xp.x)

      // sound? was: StaticSemantics.freeVars(And(dom, post))
      if (!StaticSemantics.freeVars(post).intersect(extravars.toSet).isEmpty) return None

      val vars = extravars ++ (ode1ls.map(_.asInstanceOf[AtomicODE].xp.x))

      // The goal is to sort ODE2 into extra++ODE1
      // Then add extra to ODE1
      Some(
        AxiomaticODESolver.selectionSort(dom, post, ode2, vars, SuccPosition(1))
          &
            (if (extra.isEmpty) skip else vDG(extra.reduce(DifferentialProduct.apply))(-1))
      )

    }
  }

  /**
   * Adds compatible (ODE unifiable) box modalities from the assumptions to the domain constraint e.g.
   * {{{
   * [x'=f(x)&A]B is compatible for [x'=f(x)&Q]P if A implies Q
   * [z'=g(z)&Q]P is compatible for [x'=f(x)&Q]P if z'=g(z) contains a subset of ODEs of x'=f(x)
   * }}}
   *
   * For compatible assumptions, the rule adds them by diff cut, e.g.:
   *
   * {{{
   * G, [x'=f(x)&A]B |- [x'=f(x)&Q&B]P
   * ---
   * G, [x'=f(x)&A]B |- [x'=f(x)&Q]P
   * }}}
   */
  @Tactic(
    name = "odeUnify",
    displayNameLong = Some("ODE Unify"),
    displayLevel = DisplayLevelBrowse,
    premises = "Γ, [x'=f(x)&A]B |- [x'=f(x),y'=g(y)&Q&B]P, Δ ;; A |- Q",
    conclusion = "Γ, [x'=f(x)&A]B |- [x'=f(x),y'=g(y)&Q]P, Δ",
  )
  def odeUnify: DependentPositionTactic = anon((pos: Position, seq: Sequent) => {
    if (!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("odeUnify is only applicable at a top-level succedent")

    val (tarsys, tarpost) = seq.sub(pos) match {
      case Some(Box(sys: ODESystem, post)) => (sys, post)
      case Some(e) =>
        throw new TacticInapplicableFailure("odeUnify only applicable to box ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
        )
    }

    // Loop through compatible assumptions and track the effect of DC
    var curdom = tarsys.constraint
    var curdomls = FormulaTools.conjuncts(curdom)

    var ls = new ListBuffer[(Formula, ProvableSig, Formula, Int, BelleExpr)]()

    for (i <- seq.ante.indices) {
      val asm = seq.ante(i)
      asm match {
        case Box(asmsys: ODESystem, asmpost) => if (!curdomls.contains(asmpost)) {

            compatODE(asmsys.ode, tarsys.ode, curdom, asmpost) match {
              case None => ()
              case Some(tac) => {
                val pr = proveBy(
                  Sequent(immutable.IndexedSeq(curdom), immutable.IndexedSeq(asmsys.constraint)),
                  Idioms.?(prop & done | Idioms.?(QE)),
                ) // todo: timeout?

                if (pr.isProved) {
                  ls += ((asmsys.constraint, pr, asmpost, i, tac))
                  curdom = And(curdom, asmpost)
                  curdomls = curdomls :+ asmpost
                } else ()
              }
            }
          }
        case _ => ()
      }
    }

    // println("compatible asms: ", ls)

    ls.foldLeft[BelleExpr](skip)((in, fp) => {
      val (dom, pr, f, i, tac) = (fp._1, fp._2, fp._3, fp._4, fp._5)
      in & dC(f)(pos) < (
        skip,
        cohideOnlyL(AntePosition(i + 1)) & cohideOnlyR(pos) &
          tac &
          dR(dom)(1) < (
            id,
            DifferentialTactics.diffWeakenG(1) & implyR(1) & by(pr)
          )
      )
    })
  })

  /**
   * A tiny wrapper around cut. This introduces a cut that is compatible for the ODE at a given position (regardless of
   * modality and position, although most useful for diamond ODEs)
   *
   * {{{
   * G, [x'=f(x)&Q]R |- C([x'=f(x)&Q]P)   G|-[x'=f(x)&Q]R
   * --- compatCut
   * G |- C([x'=f(x)&Q]P)
   * }}}
   */
  @Tactic(
    name = "compatCut",
    displayNameLong = Some("Compatible ODE Cut"),
    displayLevel = DisplayLevelAll,
    premises = "Γ, [x'=f(x) & Q]R |- C(⟨x'=f(x) & Q⟩P), Δ ;; Γ |- [x'=f(x) & Q]R, Δ",
    conclusion = "Γ |- C(⟨x'=f(x) & Q⟩P), Δ",
    inputs = "R:formula",
  )
  def compatCut(R: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position, seq: Sequent) =>
    {

      val (sys, post) = seq.sub(pos) match {
        case Some(Diamond(sys: ODESystem, post)) => (sys, post)
        case Some(Box(sys: ODESystem, post)) => (sys, post)
        case Some(e) =>
          throw new TacticInapplicableFailure("compatCut only applies to box/diamond of ODEs but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      cut(Box(sys, R))
    }
  }

  /**
   * Implements K<&> rule Note: uses auto cuts for the later premise
   *
   * {{{
   * G |- <ODE & Q> R
   * G |- [ODE & Q & !P] !R
   * ---- (kDomD)
   * G |- <ODE & Q> P
   * }}}
   *
   * @param R
   *   the formula R to refine the postcondition
   * @return
   *   two premises, as shown above when applied to a top-level succedent diamond
   */
  @Tactic(
    name = "kDomainDiamond",
    displayName = Some("K<&>"),
    displayLevel = DisplayLevelAll,
    premises = "Γ |- ⟨x'=f(x) & Q⟩ R, Δ ;; Γ |- [x'=f(x) & Q∧¬P]¬R, Δ",
    conclusion = "Γ |- ⟨x'=f(x) & Q⟩ P, Δ",
  )
  // was kDomD
  def kDomainDiamond(R: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position, seq: Sequent) =>
    {
      if (!(pos.isTopLevel && pos.isSucc))
        throw new IllFormedTacticApplicationException("kDomD is only applicable at a top-level succedent")

      val (sys, post) = seq.sub(pos) match {
        case Some(Diamond(sys: ODESystem, post)) => (sys, post)
        case Some(e) =>
          throw new TacticInapplicableFailure("kDomD only applicable to diamond ODEs, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      val newfml = Diamond(sys, R)

      cutR(newfml)(pos) < (
        skip & label(BelleLabels.cutUse),
        useAt(Ax.KDomD, PosInExpr(1 :: Nil))(pos) & odeUnify(pos) & label(BelleLabels.cutShow)
      )
    }
  }

  /**
   * Implements DR<.> rule Note: uses auto cuts for the later premise
   *
   * {{{
   * G |- <ODE & R> P
   * G |- [ODE & R] Q
   * ---- (dDR)
   * G |- <ODE & Q> P
   * }}}
   *
   * @param R
   *   the formula R to refine the domain constraint
   * @return
   *   two premises, as shown above when applied to a top-level succedent diamond
   */
  @Tactic(
    name = "dDR",
    displayNameLong = Some("Diamond Differential Refinement"),
    displayLevel = DisplayLevelAll,
    premises = "Γ |- ⟨x'=f(x) & R⟩P, Δ ;; Γ |- [x'=f(x) & R]Q, Δ",
    conclusion = "Γ |- ⟨x'=f(x) & Q⟩P, Δ",
  )
  def dDR(R: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position, seq: Sequent) =>
    {
      if (!(pos.isTopLevel && pos.isSucc))
        throw new IllFormedTacticApplicationException("dDR is only applicable at a top-level succedent")

      val (sys, post) = seq.sub(pos) match {
        case Some(Diamond(sys: ODESystem, post)) => (sys, post)
        case Some(e) =>
          throw new TacticInapplicableFailure("dDR only applicable to diamond ODEs, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      val newfml = Diamond(ODESystem(sys.ode, R), post)

      cutR(newfml)(pos) < (
        skip,
        useAt(Ax.DRd, PosInExpr(1 :: Nil))(pos) & odeUnify(pos)
      )
    }
  }

  /**
   * Implements linear vDG rule that adds ghosts to an ODE on the left or right, in either modality For boxes on the
   * right and diamonds on the left, the ODE must be affine
   *
   * {{{
   *   G |- [y'=g(x,y),x'=f(x)]P
   *   ---- vDG (g affine in y)
   *   G |- [x'=f(x)]P
   *
   *   [y'=g(x,y),x'=f(x)]P |- D
   *   ----
   *   [x'=f(x)]P |- D
   *
   * }}}
   *
   * @param ghost
   *   the ODEs to ghost in
   * @return
   *   the sequent with ghosts added in requested position
   */
  def vDG(ghost: DifferentialProgram): DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    {
      if (!pos.isTopLevel)
        throw new IllFormedTacticApplicationException("vDG is only applicable at a top-level position")

      val (sys, post, isBox) = seq.sub(pos) match {
        case Some(Diamond(sys: ODESystem, post)) => (sys, post, false)
        case Some(Box(sys: ODESystem, post)) => (sys, post, true)
        case Some(e) =>
          throw new TacticInapplicableFailure("vDG only applicable to box or diamond ODEs, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      // @todo: Check that ghosts are sufficiently fresh and return a nice error

      if (pos.isSucc ^ isBox) {
        val vdg = getVDGinst(ghost)._2
        if (isBox) useAt(vdg, PosInExpr(0 :: Nil))(pos)
        else // diamond in succedent
          useAt(flipModality(vdg), PosInExpr(1 :: Nil))(pos)
      } else {
        try {
          val vdg = affineVDGprecond(ghost)
          if (isBox) useAt(vdg, PosInExpr(1 :: Nil))(pos)
          else // diamond in antecedent
            useAt(flipModality(vdg), PosInExpr(0 :: Nil))(pos)
        } catch {
          case e: IllegalArgumentException => throw new TacticInapplicableFailure(
              "vDG is unable to add non-affine ghost ODEs automatically. Use dDG or bDG for nonlinear ghosts."
            )
        }
      }
    }
  }

  // Flips a proved [a]p(||) -> [b]p(||) into <b>p(||) -> <a>p(||) or vice versa, possibly with bananas for p(||)
  // Also works under 1 level of nesting and curries the result so that it is easy to apply backwards e.g.
  // foo -> [a]p(||) -> [b]p(||) into foo & <b>p(||) -> <a>p(||)
  private[btactics] def flipModality(pr: ProvableSig): ProvableSig = {

    val fml = pr.conclusion.succ(0)

    fml match {
      case Imply(Box(proga, post), Box(progb, post2)) if post == post2 => {
        proveBy(
          Imply(Diamond(progb, post), Diamond(proga, post)),
          implyR(1) &
            useAt(Ax.diamond, PosInExpr(1 :: Nil))(1) & notR(1) &
            useAt(Ax.diamond, PosInExpr(1 :: Nil))(-1) & notL(-1) &
            implyRi & byUS(pr),
        )
      }
      case Imply(Diamond(proga, post), Diamond(progb, post2)) if post == post2 => {
        proveBy(
          Imply(Box(progb, post), Box(proga, post)),
          implyR(1) &
            useAt(Ax.box, PosInExpr(1 :: Nil))(1) & notR(1) &
            useAt(Ax.box, PosInExpr(1 :: Nil))(-1) & notL(-1) &
            implyRi & byUS(pr),
        )
      }
      case Imply(outer, Imply(Box(proga, post), Box(progb, post2))) if post == post2 => {
        proveBy(
          Imply(And(outer, Diamond(progb, post)), Diamond(proga, post)),
          implyR(1) & andL(-1) &
            useAt(Ax.diamond, PosInExpr(1 :: Nil))(1) & notR(1) &
            useAt(Ax.diamond, PosInExpr(1 :: Nil))(-2) & notL(-2) &
            implyRi()(AntePos(1), SuccPos(0)) & implyRi & byUS(pr),
        )
      }
      case Imply(outer, Imply(Diamond(proga, post), Diamond(progb, post2))) if post == post2 => {
        proveBy(
          Imply(And(outer, Box(progb, post)), Box(proga, post)),
          implyR(1) & andL(-1) &
            useAt(Ax.box, PosInExpr(1 :: Nil))(1) & notR(1) &
            useAt(Ax.box, PosInExpr(1 :: Nil))(-2) & notL(-2) &
            implyRi()(AntePos(1), SuccPos(0)) & implyRi & byUS(pr),
        )
      }
      case _ => ???
    }
  }

  private def byUScaught(p: ProvableSig) = TryCatch(
    byUS(p),
    classOf[UnificationException],
    (ex: UnificationException) => throw new TacticInapplicableFailure("Un-unifiable with: " + p + " Exception:" + ex),
  )

  private def byUScaught(p: Lemma) = TryCatch(
    byUS(p),
    classOf[UnificationException],
    (ex: UnificationException) => throw new TacticInapplicableFailure("Un-unifiable with: " + p + " Exception:" + ex),
  )

  private def byUScaught(p: ProvableInfo) = TryCatch(
    byUS(p),
    classOf[UnificationException],
    (ex: UnificationException) => throw new TacticInapplicableFailure("Un-unifiable with: " + p + " Exception:" + ex),
  )

  /**
   * Implements dV rule for atomic postconditions The bottom two premises are auto-closed because of the need to
   * Dconstify The first one is partially auto-closed if odeReduce is able to prove global existence e.g. (similarly for
   * dV >),
   *
   * Note: autonormalizes to >= and > (but provided e_() must be for the normalized shape!)
   *
   * {{{
   * G, t=0 |- <t'=1, ODE & Q> t > const
   * G, t=0 |- e_() > 0
   * G, t=0 |- [t'=1, ODE & Q & p-q < 0] p'-q' >= e () (this uses compatible cuts )
   * ---- (dV >=)
   * G |- <ODE & Q> p >= q
   * }}}
   *
   * Note that domain constraint Q is kept around!
   *
   * @param bnd
   *   the lower bound on derivatives
   * @param manual
   *   whether to try closing automatically
   * @return
   *   closes (or partially so)
   */
  def dV(bnd: Term, manual: Boolean = false): DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    {
      if (!pos.isTopLevel)
        throw new IllFormedTacticApplicationException("dV is only applicable at a top-level succedent")

      val (sys, post) = seq.sub(pos) match {
        case Some(Diamond(sys: ODESystem, post)) => (sys, post)
        // @todo Illformed if diamond in antecedent?
        case Some(e) =>
          throw new TacticInapplicableFailure("dV only applicable to diamond ODEs, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      if (!StaticSemantics.boundVars(sys).intersect(StaticSemantics.freeVars(bnd)).isEmpty)
        throw new IllFormedTacticApplicationException("Bound " + bnd + " must be constant for ODE " + sys.ode + ".")

      val (property, propt) = ineqNormalize(post)

      val starter = propt match {
        case None => skip
        case Some(pr) => useAt(pr)(pos ++ PosInExpr(1 :: Nil))
      }

      // support for old
      val timevar = TacticHelper.freshNamedSymbol("t".asVariable, seq)

      val timer = AtomicODE(DifferentialSymbol(timevar), Number(1))

      // Introduces the time variable in a mildly gross way so that it is set to 0 initially
      val timetac = cut(Exists(List(timevar), Equal(timevar, Number(0)))) < (
        existsL(Symbol("Llast")), cohideR(Symbol("Rlast")) & QE
      ) &
        vDG(timer)(pos)

      val p = property.sub(PosInExpr(0 :: Nil)).get.asInstanceOf[Term]
      val oldp = TacticHelper.freshNamedSymbol("oldp".asVariable, seq)

      val unifODE = UnificationMatch("{c &q_(||)}".asProgram, sys).usubst
      val unify = UnificationMatch("p(||) + e_()".asTerm, Plus(oldp, bnd)).usubst

      val ax = property match {
        case Greater(_, _) => DVgt.fact
        case GreaterEqual(_, _) => DVgeq.fact
        case _ => ??? // impossible
      }

      val axren = ax(URename(timevar, "t".asVariable, semantic = true))(unifODE)(unify)

      val ex = property match {
        case Greater(_, _) => Ax.TExgt
        case GreaterEqual(_, _) => Ax.TExge
        case _ => ??? // impossible
      }

      starter & timetac &
        discreteGhost(p, Some(oldp))(pos) &
        useAt(axren, PosInExpr(1 :: Nil))(pos) &
        (if (manual) skip
         else andR(pos) < (
           andR(pos) < (
             ToolTactics.hideNonFOL & QE &
               DebuggingTactics.done("Unable to prove " + bnd + " strictly positive."), // G |- e_() > 0
             odeReduce(strict = false, Nil)(pos) &
               Idioms.?(cohideR(pos) & byUScaught(ex))
           ), // existence
           (odeUnify(pos) & dI(Symbol("full"))(pos) & done |
             skip)
           // DebuggingTactics.done("Unable to prove derivative lower bound using "+ bnd +".")
           // derivative lower bound
         ))
    }
  }

  // A more "auto"matic but slower/less flexible version of dV
  def dVAuto(autoqe: Boolean = true): DependentPositionTactic = anon((pos: Position, seq: Sequent) => {
    if (!pos.isTopLevel) throw new IllFormedTacticApplicationException("dV is only applicable at a top-level succedent")

    val (sys, post) = seq.sub(pos) match {
      case Some(Diamond(sys: ODESystem, post)) => (sys, post)
      // @todo Illformed if diamond on antecedent?
      case Some(e) =>
        throw new TacticInapplicableFailure("dV only applicable to diamond ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
        )
    }

    val odels = DifferentialProduct
      .listify(sys.ode)
      .map {
        case AtomicODE(x, e) => (x, e)
        case _ => throw new TacticInapplicableFailure("dVAuto only applicable to concrete ODEs")
      }

    val eps = TacticHelper.freshNamedSymbol("eps".asVariable, seq)
    val bvs = odels.map(_._1.x)

    // e > 0
    val eg0 = Greater(eps, Number(0))
    // p' >= e
    val lie = post match {
      case Greater(l, r) => GreaterEqual(simplifiedLieDerivative(sys.ode, Minus(l, r), None), eps)
      case GreaterEqual(l, r) => GreaterEqual(simplifiedLieDerivative(sys.ode, Minus(l, r), None), eps)
      case Less(l, r) => GreaterEqual(simplifiedLieDerivative(sys.ode, Minus(r, l), None), eps)
      case LessEqual(l, r) => GreaterEqual(simplifiedLieDerivative(sys.ode, Minus(r, l), None), eps)
      case _ => throw new TacticInapplicableFailure(
          "dVAuto expects only atomic inequality (>,>=,<,<=) in succedent (try semialgdV)"
        )
    }

    // (Q & p < 0 -> p' >= e)
    // val liecheck = Imply(And(sys.constraint,Not(post)),lie)
    // \\exists e (e > 0 & \\forall x (Q & p < 0 -> p' >= e))
    // val qe = Exists(eps::Nil, bvs.foldRight(And(eg0,liecheck):Formula)( (v,f) => Forall(v::Nil,f)))
    // val pr = proveBy(seq.updated(pos.checkTop,qe), ToolTactics.hideNonFOL & QE)

    // This more accurately finds the compatible cuts by simulating it in action
    val prpre = proveBy(seq, dV(Number(0), true)(pos) & andR(pos) < (skip, odeUnify(pos)))
    val dom = prpre.subgoals(1).sub(pos ++ PosInExpr(0 :: 1 :: Nil)).get.asInstanceOf[Formula]
    // (dom (with compat cuts) -> p' >= e)
    val liecheck = Imply(dom, lie)
    val quantliecheck = bvs.foldRight(liecheck: Formula)((v, f) => Forall(v :: Nil, f))
    // \\exists e (e > 0 & \\forall x (dom -> p' >= e))
    val qe = Exists(eps :: Nil, And(eg0, quantliecheck))

    val tac = ToolTactics.hideNonFOL & (if (autoqe) QE else skip)

    // val pr = proveBy(seq.updated(pos.checkTop,qe), )

    // if(!pr.isProved)
    //  throw new TacticInapplicableFailure("dVAuto failed to prove arithmetic condition: " + qe)

    cutR(qe)(pos) < (
      label(BelleLabels.dVderiv) & tac,
      implyR(pos) & existsL(Symbol("Llast")) & andL(Symbol("Llast")) & dV(eps, true)(pos) &
        andR(pos) < (
          andR(pos) < (
            id,
            // hide the eps assumptions
            label(BelleLabels.dVexists) &
              hideL(-(seq.ante.length + 1)) & hideL(-(seq.ante.length + 1)) &
              odeReduce(strict = false, Nil)(pos) & Idioms
                .?(cohideR(pos) & (byUScaught(Ax.TExge) | byUScaught(Ax.TExgt)))
          ), // existence
          odeUnify(pos) &
            dR(lie, false)(pos) < (
              cohideOnlyR(pos) & (hideL(-1) * (seq.ante.length + 2)) & dI(Symbol("full"))(1),
              // add the quantified assumption manually
              dC(quantliecheck)(pos) < (
                DifferentialTactics.diffWeakenG(pos) & implyR(1) & andL(-1) & (allL(Symbol("Llast")) * bvs
                  .length) & implyL(Symbol("Llast")) < (
                  id,
                  id
                ),
                V(pos) & id
              )
            ) // derivative lower bound
        )
    )
  })

  // Semialgebraic dV
  def semialgdV(bnd: Term): DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    {
      if (!pos.isTopLevel)
        throw new IllFormedTacticApplicationException("dV is only applicable at a top-level succedent")

      val (sys, post) = seq.sub(pos) match {
        case Some(Diamond(sys: ODESystem, post)) => (sys, post)
        // @todo Illformed if diamond in antecedent?
        case Some(e) =>
          throw new TacticInapplicableFailure("semialgdV only applicable to diamond ODEs, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      val (property, propt) = SimplifierV3.semiAlgNormalize(post)

      val starter = propt match {
        case None => skip
        case Some(pr) => useAt(pr)(pos ++ PosInExpr(1 :: Nil))
      }

      // support for old
      val timevar = TacticHelper.freshNamedSymbol("t".asVariable, seq)

      val timer = AtomicODE(DifferentialSymbol(timevar), Number(1))

      // Introduces the time variable in a mildly gross way so that it is set to 0 initially
      val timetac = cut(Exists(List(timevar), Equal(timevar, Number(0)))) < (
        existsL(Symbol("Llast")), cohideR(Symbol("Rlast")) & QE
      ) &
        vDG(timer)(pos)

      // Symbolic lower bound
      val oldp = TacticHelper.freshNamedSymbol("oldp".asVariable, seq)

      val oldpbound = Greater(Plus(oldp, Times(bnd, timevar)), Number(0))

      def mkFml(fml: Formula): Formula = {
        fml match {
          case Greater(p, _) => GreaterEqual(Minus(p, Plus(oldp, Times(bnd, timevar))), Number(0))
          case GreaterEqual(p, _) => GreaterEqual(Minus(p, Plus(oldp, Times(bnd, timevar))), Number(0))
          case And(l, r) => And(mkFml(l), mkFml(r))
          case Or(l, r) => Or(mkFml(l), mkFml(r))
          case _ => throw new TacticInapplicableFailure(
              "Unable to normalize postcondition to conjunction/disjunction of >, >=. Attempted normalization: " + fml
            )
        }
      }

      val inv = mkFml(property)

      // Pre-unify to avoid Dconstify
      val unifODE = UnificationMatch("{c &q_(||)}".asProgram, sys).usubst
      val unify = UnificationMatch("p(||) + e_()".asTerm, Plus(oldp, bnd)).usubst

      val axren = exRWgt.fact(URename(timevar, "t".asVariable, semantic = true))(unifODE)(unify)

      starter & timetac &
        cut(Exists(List(oldp), inv)) < (
          existsL(Symbol("Llast")),
          cohideR(Symbol("Rlast")) & QE // this should be a trivial QE question
        ) &
        kDomainDiamond(oldpbound)(pos) < (
          useAt(axren, PosInExpr(1 :: Nil))(pos) & andR(pos) < (
            ToolTactics.hideNonFOL & QE,
            odeReduce(strict = false, Nil)(pos) & Idioms.?(cohideR(pos) & byUScaught(Ax.TExgt))
          ), // existence
          dC(inv)(pos) < (
            DW(pos) & G(pos) & ToolTactics.hideNonFOL & QE, // can be proved manually
            DifferentialTactics
              .DconstV(pos) & sAIclosed(pos) & done | // ODE does a boxand split, which is specifically a bad idea here
              skip
          )
        )

    }
  }

  // Semialgebraic dV
  def semialgdVAuto(autoqe: Boolean = true): DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    {
      if (!pos.isTopLevel)
        throw new IllFormedTacticApplicationException("dV is only applicable at a top-level succedent")

      val (sys, post) = seq.sub(pos) match {
        case Some(Diamond(sys: ODESystem, post)) => (sys, post)
        // @todo Illformed if diamond in antecedent?
        case Some(e) => throw new TacticInapplicableFailure(
            "semialgdVAuto only applicable to diamond ODEs, but got " + e.prettyString
          )
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      val (property, propt) = SimplifierV3.semiAlgNormalize(post)

      val starter = propt match {
        case None => skip
        case Some(pr) => useAt(pr)(pos ++ PosInExpr(1 :: Nil))
      }

      // support for old
      val timevar = TacticHelper.freshNamedSymbol("t".asVariable, seq)

      val timer = AtomicODE(DifferentialSymbol(timevar), Number(1))

      // Introduces the time variable in a mildly gross way so that it is set to 0 initially
      val timetac = cut(Exists(List(timevar), Equal(timevar, Number(0)))) < (
        existsL(Symbol("Llast")), cohideR(Symbol("Rlast")) & QE
      ) &
        vDG(timer)(pos)

      val eps = TacticHelper.freshNamedSymbol("eps".asVariable, seq)
      val eg0 = Greater(eps, Number(0))

      // Symbolic lower bound
      val oldp = TacticHelper.freshNamedSymbol("oldp".asVariable, seq)

      val oldpbound = Greater(Plus(oldp, Times(eps, timevar)), Number(0))

      def mkFml(fml: Formula): Formula = {
        fml match {
          case Greater(p, _) => GreaterEqual(Minus(p, Plus(oldp, Times(eps, timevar))), Number(0))
          case GreaterEqual(p, _) => GreaterEqual(Minus(p, Plus(oldp, Times(eps, timevar))), Number(0))
          case And(l, r) => And(mkFml(l), mkFml(r))
          case Or(l, r) => Or(mkFml(l), mkFml(r))
          case _ => throw new TacticInapplicableFailure(
              "Unable to normalize postcondition to conjunction/disjunction of >, >=. Attempted normalization: " + fml
            )
        }
      }

      // Pre-unify to avoid Dconstify
      val unifODE = UnificationMatch("{c &q_(||)}".asProgram, sys).usubst
      val unify = UnificationMatch("p(||) + e_()".asTerm, Plus(oldp, eps)).usubst

      val axren = exRWgt.fact(URename(timevar, "t".asVariable, semantic = true))(unifODE)(unify)

      val inv = mkFml(property)
      val sim = proveBy(
        seq,
        starter & timetac &
          kDomainDiamond(oldpbound)(pos) < (
            skip,
            dC(inv)(pos) < (
              skip,
              DifferentialTactics.DconstV(pos)
            )
          ),
      )

      val simseq = sim.subgoals.last
      val (sysex: DifferentialProgram, domex) = simseq.sub(pos) match {
        case Some(Box(ODESystem(s, d), _)) => (s, d)
        case _ => (sys.ode, True) // cannot happen
      }

      val odels = DifferentialProduct
        .listify(sysex)
        .map {
          case AtomicODE(x, e) => (x, e)
          case _ => throw new TacticInapplicableFailure("semialgdVAuto only applicable to concrete ODEs")
        }
      val bvs = odels.map(_._1.x)

      val invstar = fStar(ODESystem(sysex, domex), inv)._1

      val liecheck = Imply(And(domex, inv), invstar)
      val quantliecheck1 = bvs.foldRight(liecheck: Formula)((v, f) => Forall(v :: Nil, f))
      val quantliecheck = Forall(oldp :: Nil, quantliecheck1)
      // \\exists e (e > 0 & \\forall x (dom -> p' >= e))
      val qe = Exists(eps :: Nil, And(eg0, quantliecheck))

      val tac = ToolTactics.hideNonFOL & (if (autoqe) QE else skip)

      starter & timetac &
        cutR(qe)(pos) < (
          label(BelleLabels.dVderiv) & tac,
          implyR(pos) & existsL(Symbol("Llast")) & andL(Symbol("Llast")) &
            cut(Exists(List(oldp), inv)) < (
              existsL(Symbol("Llast")) & allL(-(seq.ante.length + 3)),
              cohideR(Symbol("Rlast")) & QE // this should be a trivial QE question
            ) &
            kDomainDiamond(oldpbound)(pos) < (
              hideL(-(seq.ante.length + 3)) &
                useAt(axren, PosInExpr(1 :: Nil))(pos) & andR(pos) < (
                  ToolTactics.hideNonFOL & QE,
                  label(BelleLabels.dVexists) & odeReduce(strict = false, Nil)(pos) & Idioms
                    .?(cohideR(pos) & byUScaught(Ax.TExgt))
                ), // existence
              dC(inv)(pos) < (
                DW(pos) & G(pos) & ToolTactics.hideNonFOL & QE, // can be proved manually
                dC(liecheck)(pos) < (
                  hideL(-(seq.ante.length + 3)) &
                    DifferentialTactics.DconstV(pos) & sAIclosed(pos),
                  // add the quantified assumption manually
                  dC(quantliecheck1)(pos) < (
                    DifferentialTactics.diffWeakenG(pos) &
                      implyR(1) & andL(-1) & (allL(Symbol("Llast")) * bvs.length) &
                      id,
                    V(pos) & id
                  )
                )
              )
            )
        )

    }
  }

  /** some of these should morally be in DerivedAxioms but have weird dependencies */
  private lazy val exRWgt = remember(
    "e_() > 0 & <{t'=1, c &q_(||)}> t > -p(||)/e_() -> <{t'=1, c &q_(||)}> p(||) + e_() * t > 0".asFormula,
    implyR(1) & andL(-1) &
      cutR("<{t'=1,c&q_(||)}>(t>-p(||)/e_() & e_() > 0)".asFormula)(1) < (
        implyRi()(AntePosition(2), SuccPosition(1)) & useAt(Ax.KDomD, PosInExpr(1 :: Nil))(1) &
          cutR("[{t'=1,c&(q_(||)&!(t>-p(||)/e_()&e_()>0)) & e_() > 0}](!t>-p(||)/e_())".asFormula)(1) < (
            DW(1) & G(1) & prop,
            equivifyR(1) & commuteEquivR(1) &
              useAt(Ax.DC, PosInExpr(1 :: Nil))(1) & V(1) & id
          ),
        cohideR(1) & implyR(1) & mond & byUS(proveBy("t>-p()/e_()&e_()>0 ==> p()+e_()*t>0".asSequent, QE))
      ),
    namespace,
  )

  private lazy val exRWge = remember(
    "e_() > 0 & <{t'=1, c &q_(||)}> t >= -p(||)/e_() -> <{t'=1, c &q_(||)}> p(||) + e_() * t >= 0".asFormula,
    implyR(1) & andL(-1) &
      cutR("<{t'=1,c&q_(||)}>(t>=-p(||)/e_() & e_() > 0)".asFormula)(1) < (
        implyRi()(AntePosition(2), SuccPosition(1)) & useAt(Ax.KDomD, PosInExpr(1 :: Nil))(1) &
          cutR("[{t'=1,c&(q_(||)&!(t>=-p(||)/e_()&e_()>0)) & e_() > 0}](!t>=-p(||)/e_())".asFormula)(1) < (
            DW(1) & G(1) & prop,
            equivifyR(1) & commuteEquivR(1) &
              useAt(Ax.DC, PosInExpr(1 :: Nil))(1) & V(1) & id
          ),
        cohideR(1) & implyR(1) & mond & byUS(proveBy("t>=-p()/e_()&e_()>0 ==> p()+e_()*t>=0".asSequent, QE))
      ),
    namespace,
  )

  private lazy val DVgeq = remember(
    "(e_() > 0 & <{t'=1, c &q_(||)}> t >= -p(||)/e_()) & [{t'=1, c & q_(||) & f_(||) < 0}] f_(||) >= p(||) + e_() * t -> <{t'=1, c & q_(||)}> f_(||) >= 0"
      .asFormula,
    implyR(1) & andL(-1) & useAt(exRWge.fact, PosInExpr(0 :: Nil))(-1) & implyRi &
      useAt(Ax.KDomD, PosInExpr(1 :: Nil))(1) &
      cutR("[{t'=1,c&(q_(||)&!f_(||)>=0)&f_(||) >= p(||) + e_() * t}](!p(||) + e_()* t >= 0)".asFormula)(1) < (
        DW(1) & G(1) & prop & hideL(Symbol("L"), "q_(||)".asFormula) & byUS(
          proveBy("f_()>=p()+e_()*t, p()+e_()*t>=0 ==> f_()>=0".asSequent, QE)
        ),
        equivifyR(1) & commuteEquivR(1) &
          useAt(Ax.DC, PosInExpr(1 :: Nil))(1) &
          useAt(Ax.notGreaterEqual, PosInExpr(0 :: Nil))(1, 0 :: 1 :: 1 :: Nil) & id
      ),
    namespace,
  )

  private lazy val DVgt = remember(
    "(e_() > 0 & <{t'=1, c &q_(||)}> t > -p(||)/e_()) & [{t'=1, c & q_(||) & f_(||) <= 0}] f_(||) >= p(||) + e_() * t -> <{t'=1, c & q_(||)}> f_(||) > 0"
      .asFormula,
    implyR(1) & andL(-1) & useAt(exRWgt.fact, PosInExpr(0 :: Nil))(-1) & implyRi &
      useAt(Ax.KDomD, PosInExpr(1 :: Nil))(1) &
      cutR("[{t'=1,c&(q_(||)&!f_(||)>0)&f_(||) >= p(||) + e_() * t}](!p(||) + e_()* t > 0)".asFormula)(1) < (
        DW(1) & G(1) & prop & hideL(Symbol("L"), "q_(||)".asFormula) & byUS(
          proveBy("f_()>=p()+e_()*t, p()+e_()*t>0 ==> f_()>0".asSequent, QE)
        ),
        equivifyR(1) & commuteEquivR(1) &
          useAt(Ax.DC, PosInExpr(1 :: Nil))(1) &
          useAt(Ax.notGreater, PosInExpr(0 :: Nil))(1, 0 :: 1 :: 1 :: Nil) & id
      ),
    namespace,
  )

  /**
   * Implements higher dV series rule for atomic postconditions with less automation Given a series a_0, a_1, ... , a_n
   * :
   *
   * {{{
   * G |- [t'=1, ODE&Q & p<0] p >= a_0 + a_1 t + a_2 t^2 + ... + a_n t^n
   * G |- <t'=1, ODE & Q> a_0 + a_1 t + a_2 t^2 + ... + a_n t^n > 0
   * ---- (higherdV >=)
   * G |- <ODE & Q> p >= 0
   * }}}
   *
   * Note that domain constraint Q is kept around!
   *
   * @param bnds
   *   the lower bound on derivatives
   * @return
   *   two subgoals, shown above
   */
  def higherdV(bnds: List[Term]): DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    {
      if (!pos.isTopLevel)
        throw new IllFormedTacticApplicationException("Higher dV is only applicable at a top-level succedent")

      val (sys, post) = seq.sub(pos) match {
        case Some(Diamond(sys: ODESystem, post)) => (sys, post)
        // @todo Illformed if diamond in antecedent?
        case Some(e) =>
          throw new TacticInapplicableFailure("higherdV only applicable to diamond ODEs, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      val (property, propt) = ineqNormalize(post)

      val starter = propt match {
        case None => skip
        case Some(pr) => useAt(pr)(pos ++ PosInExpr(1 :: Nil))
      }

      // support for old
      val timevar = TacticHelper.freshNamedSymbol("t".asVariable, seq)
      val timer = AtomicODE(DifferentialSymbol(timevar), Number(1))

      // Introduces the time variable in a mildly gross way so that it is set to 0 initially
      val timetac = cut(Exists(List(timevar), Equal(timevar, Number(0)))) < (
        existsL(Symbol("Llast")), cohideR(Symbol("Rlast")) & QE
      ) &
        vDG(timer)(pos)

      val p = property.sub(PosInExpr(0 :: Nil)).get.asInstanceOf[Term]

      // todo: directly support old(.) in term list instead of baking it in
      // should coeff be baked in or not?
      val coeff = TacticHelper.freshNamedSymbol("coeff".asVariable, seq)
      val coefflist = bnds.indices.map(i => Variable(coeff.name + i))
      val coefftac = (bnds zip coefflist).map(bc => discreteGhost(bc._1, Some(bc._2))(pos): BelleExpr).reduce(_ & _)

      val series = coefflist
        .tail
        .zipWithIndex
        .foldLeft(coefflist.head: Term) { (h, fe) => Plus(h, Times(fe._1, Power(timevar, Number(fe._2 + 1)))) }

      val ex = property match {
        case Greater(_, _) => Ax.TExgt
        case GreaterEqual(_, _) => Ax.TExge
        case _ => ??? // impossible
      }

      starter & timetac & coefftac &
        kDomainDiamond(property.asInstanceOf[ComparisonFormula].reapply(series, Number(0)))(pos) < (
          odeReduce(strict = false, Nil)(pos) & Idioms.?(solve(pos) & QE),
          dC(GreaterEqual(p, series))(pos) < (
            DW(pos) & G(pos) & QE // might as well have usubst here
            ,
            skip
          )
        )
//      discreteGhost(p, Some(oldp))(pos) &
//      useAt(axren,PosInExpr(1::Nil))(pos) &
//      andR(pos) < (
//        ToolTactics.hideNonFOL & QE //G |- e_() > 0
//        ,
//        andR(pos) <(
//          odeReduce(strict = false)(pos) & Idioms.?(cohideR(pos) & byUS(ex)), // existence
//          compatCuts(pos) & dI('full)(pos)  // derivative lower bound
//        )
//      )
    }
  }

  /**
   * Saves a (negated) box version of the liveness postcondition. This is a helpful pattern because of compat cuts
   *
   * {{{
   * G, [ODE & Q]!P |- <ODE & Q> P
   * ---- (saveBox)
   * G |- <ODE & Q> P
   * }}}
   */
  def saveBox: DependentPositionTactic = anon((pos: Position, seq: Sequent) => {
    if (!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("saveBox is only applicable at a top-level succedent")

    val (tarsys, tarpost) = seq.sub(pos) match {
      case Some(Diamond(sys: ODESystem, post)) => (sys, post)
      // @todo Illformed if diamond in antecedent?
      case Some(e) =>
        throw new TacticInapplicableFailure("saveBox only applicable to diamond ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
        )
    }

    cut(Box(tarsys, Not(tarpost))) < (
      skip,
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(pos) & notR(pos) & id
    )
  })

  /**
   * ODE diamond is true if domain and postcondition was already true initially
   *
   * {{{
   * G |- Q & P
   * ----
   * G |- <x'=f(x)&Q>P
   * }}}
   *
   * @return
   *   see rule above
   */
  def dDX: BuiltInPositionTactic = useAt(Ax.dDX)

  /**
   * Refinement for a closed domain constraint (e.g. Q = p>=0)
   *
   * {{{
   * G |- <ODE & R> P
   * G |- p>0 //must start in interior of domain
   * G |-[ODE & R & p>=0 & !P] p>0 //must stay in interior of domain except by possibly exiting exactly at the end
   * ---- (closedRefine)
   * G |- <ODE & p>=0> P
   * }}}
   *
   * @todo:
   *   succeeds but probably unexpectedly when Q is not closed. Best to error instead.
   */

  @Tactic(
    name = "closedRef",
    displayNameLong = Some("Closed Domain Refinement"),
    displayLevel = DisplayLevelBrowse,
    premises = "Γ |- ⟨x'=f(x) & R⟩P, Δ ;; Γ |- g>0 & [x'=f(x) & R∧¬P∧g≳0]g>0, Δ",
    conclusion = "Γ |- ⟨x'=f(x) & g≳0⟩P, Δ",
  )
  def closedRef(R: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position, seq: Sequent) =>
    {
      if (!(pos.isTopLevel && pos.isSucc))
        throw new IllFormedTacticApplicationException("closedRef is only applicable at a top-level succedent")

      val (sys, post) = seq.sub(pos) match {
        case Some(Diamond(sys: ODESystem, post)) => (sys, post)
        // @todo Illformed if diamond in antecedent?
        case Some(e) =>
          throw new TacticInapplicableFailure("closedRef only applicable to diamond ODEs, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      saveBox(pos) & dDR(R)(pos) < (
        // Remove the saveBox to reduce clutter
        hideL(Symbol("Llast")),
        DifferentialTactics.dCClosure(pos) < (
          hideL(Symbol("Llast")) & skip,
          odeUnify(pos) & hideL(Symbol("Llast"))
        )
      )
    }
  }

  private lazy val curry = remember("(p() -> (q() -> r())) <-> (p()&q()->r())".asFormula, prop, namespace)

  /**
   * Implements dDG rule that adds ghosts to box ODEs on the right of the turnstile
   *
   * {{{
   * G |- [ghosts, ODE] (||ghosts||)' <= L ||ghosts|| + M
   * G |- [ghosts, ODE]P
   * ---- dDG
   * G |- [ODE]P
   * }}}
   *
   * @param ghost
   *   the ghost ODEs, L, M as above
   */
  def dDG(ghost: DifferentialProgram, L: Term, M: Term): DependentPositionTactic =
    anon((pos: Position, seq: Sequent) => {
      require(pos.isTopLevel && pos.isSucc, "dDG is only applicable at a top-level succedent")

      val (sys, post) = seq.sub(pos) match {
        case Some(Box(sys: ODESystem, post)) => (sys, post)
        case Some(e) =>
          throw new TacticInapplicableFailure("dDG only applicable to box ODE in succedent, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
          )
      }

      val ddgpre = getDDGinst(ghost)

      val lipsLsub = ddgpre.conclusion.succ(0).sub(PosInExpr(0 :: 1 :: 1 :: 0 :: 0 :: Nil)).get
      val lipsMsub = ddgpre.conclusion.succ(0).sub(PosInExpr(0 :: 1 :: 1 :: 1 :: Nil)).get

      val lipsLunif = UnificationMatch.unifiable(lipsLsub, L).get.usubst
      val lipsMunif = UnificationMatch.unifiable(lipsMsub, M).get.usubst
      val ddg = (ddgpre(lipsLunif))(lipsMunif)

      useAt(useFor(curry, PosInExpr(0 :: Nil), ((us: Subst) => us))(Position(1))(ddg), PosInExpr(1 :: Nil))(pos) & andR(
        pos
      )
    })

  /**
   * Implements bDG rule that adds ghosts to box ODEs on the right of the turnstile
   *
   * {{{
   * G |- [ghosts, ODE] (||ghosts||)^2 <= p
   * G |- [ghosts, ODE]P
   * ---- dDG
   * G |- [ODE]P
   * }}}
   *
   * @param ghost
   *   the ghost ODEs, L, M as above
   */
  def bDG(ghost: DifferentialProgram, p: Term): DependentPositionTactic = anon((pos: Position, seq: Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "bDG is only applicable at a top-level succedent")

    val (sys, post) = seq.sub(pos) match {
      case Some(Box(sys: ODESystem, post)) => (sys, post)
      case Some(e) =>
        throw new TacticInapplicableFailure("bDG only applicable to box ODE in succedent, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
        )
    }

    val vdgpre = getVDGinst(ghost)._1
    val vdgsubst = UnificationMatch(vdgpre.conclusion.succ(0).sub(PosInExpr(0 :: 1 :: 1 :: Nil)).get, p).usubst
    // the concrete vdg instance
    val vdg = vdgpre(vdgsubst)

    useAt(useFor(curry, PosInExpr(0 :: Nil), ((us: Subst) => us))(Position(1))(vdg), PosInExpr(1 :: Nil))(pos) & andR(
      pos
    )
  })

  /** Wrapper around bDG for display. */
  @Tactic(
    name = "bDG",
    displayNameLong = Some("Bounded Differential Ghost"),
    displayLevel = DisplayLevelBrowse,
    premises = "Γ |- [ghost, x'=f(x) & Q] (||ghost||)^2 <= p, Δ ;; [ghost, x'=f(x) & Q]P, Δ",
    conclusion = "Γ |- [{x'=f(x) & Q}]P, Δ",
    inputs = "ghost:expression ;; p:term",
  )
  def bDG(ghost: Expression, p: Term): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    ghost match {
      case Equal(l: DifferentialSymbol, r) => ODELiveness.bDG(AtomicODE(l, r), p)(pos)
      case dp: DifferentialProgram => ODELiveness.bDG(dp, p)(pos)
      case ODESystem(dp, _) => ODELiveness.bDG(dp, p)(pos)
      case _ =>
        throw new IllegalArgumentException("Expected a differential program y′=f(y), but got " + ghost.prettyString)
    }
  }

  /** Wrapper around vDG for display. */
  @Tactic(
    name = "vDG",
    displayNameLong = Some("Affine Vectorial Differential Ghost"),
    displayLevel = DisplayLevelBrowse,
    premises = "Γ |- [ghost, x'=f(x) & Q]P, Δ",
    conclusion = "Γ |- [{x'=f(x) & Q}]P, Δ",
    inputs = "ghost:expression",
  )
  def vDG(ghost: Expression): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    ghost match {
      case Equal(l: DifferentialSymbol, r) => ODELiveness.vDG(AtomicODE(l, r))(pos)
      case dp: DifferentialProgram => ODELiveness.vDG(dp)(pos)
      case ODESystem(dp, _) => ODELiveness.vDG(dp)(pos)
      case _ =>
        throw new IllegalArgumentException("Expected a differential program y′=f(y), but got " + ghost.prettyString)
    }
  }

  /**
   * dDDG rule
   *
   * {{{
   * G |- [ghosts, ODE] (||ghosts||)' <= L ||ghosts|| + M
   * G |- <ODE & R> P
   * ---- (dDDG)
   * G |- <ghosts , ODE & p>=0> P
   * }}}
   *
   * @param L,
   *   M as above
   * @param dim
   *   The first dim ODEs at the given position are treated as ghosts
   */
  private def dDDGInternal(L: Term, M: Term, dim: Int = 1)(pos: Position, seq: Sequent) = {
    require(pos.isTopLevel && pos.isSucc, "dDDG is only applicable at a top-level succedent")
    require(dim >= 1, "dDDG must remove at least 1 ghost ODE")

    val (sys, post) = seq.sub(pos) match {
      case Some(Diamond(sys: ODESystem, post)) => (sys, post)
      case Some(e) =>
        throw new TacticInapplicableFailure("dDDG only applicable to diamond ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
        )
    }

    val odels = DifferentialProduct
      .listify(sys.ode)
      .map {
        case AtomicODE(x, e) => AtomicODE(x, e)
        case ode =>
          throw new TacticInapplicableFailure("dDDG only applicable to concrete ODEs, but got " + ode.prettyString)
      }

    // Must have at least 1 ODE left after ghosting
    if (odels.length < dim + 1)
      throw new IllFormedTacticApplicationException("Too few ghost ODEs to remove: " + sys.ode.prettyString)

    val ghosts = odels.take(dim)

    // todo: refactor this code out somehow to reduce duplication
    val ddgpre = getDDGinst(ghosts.reduce(DifferentialProduct.apply))

    val lipsLsub = ddgpre.conclusion.succ(0).sub(PosInExpr(0 :: 1 :: 1 :: 0 :: 0 :: Nil)).get
    val lipsMsub = ddgpre.conclusion.succ(0).sub(PosInExpr(0 :: 1 :: 1 :: 1 :: Nil)).get

    val lipsLunif = UnificationMatch.unifiable(lipsLsub, L).get.usubst
    val lipsMunif = UnificationMatch.unifiable(lipsMsub, M).get.usubst
    val ddg = (ddgpre(lipsLunif))(lipsMunif)
    val ddgf = flipModality(ddg)

    useAt(ddgf, PosInExpr(1 :: Nil))(pos) & andR(pos)
  }

  def dDDG(L: Term, M: Term, dim: Int): DependentPositionTactic =
    anon((pos: Position, sequent: Sequent) => dDDGInternal(L, M, dim)(pos, sequent))

  /**
   * dBDG rule
   *
   * {{{
   * G |- [ghosts, ODE] (||ghosts||)^2 <= p
   * G |- <ODE & R> P
   * ---- (dBDG)
   * G |- <ghosts , ODE & R> P
   * }}}
   *
   * @param p
   *   as above
   * @param dim
   *   The first dim ODEs at the given position are treated as ghosts
   */
  private def dBDGInternal(p: Term, dim: Int = 1)(pos: Position, seq: Sequent) = {
    require(pos.isTopLevel && pos.isSucc, "dBDG is only applicable at a top-level succedent")
    require(dim >= 1, "dBDG must remove at least 1 ghost ODE")

    val (sys, post) = seq.sub(pos) match {
      case Some(Diamond(sys: ODESystem, post)) => (sys, post)
      case Some(e) =>
        throw new TacticInapplicableFailure("dBDG only applicable to diamond ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + seq.prettyString
        )
    }

    val odels = DifferentialProduct
      .listify(sys.ode)
      .map {
        case AtomicODE(x, e) => AtomicODE(x, e)
        case ode =>
          throw new TacticInapplicableFailure("dBDG only applicable to concrete ODEs, but got " + ode.prettyString)
      }

    // Must have at least 1 ODE left after ghosting
    if (odels.length < dim + 1)
      throw new IllFormedTacticApplicationException("Too few ghost ODEs to remove: " + sys.ode.prettyString)

    val ghosts = odels.take(dim)

    // todo: refactor this code out somehow to reduce duplication
    val vdgpre = getVDGinst(ghosts.reduce(DifferentialProduct.apply))._1
    val vdgsubst = UnificationMatch(vdgpre.conclusion.succ(0).sub(PosInExpr(0 :: 1 :: 1 :: Nil)).get, p).usubst
    // the concrete vdg instance
    val vdg = vdgpre(vdgsubst)
    val vdgf = flipModality(vdg)

    useAt(vdgf, PosInExpr(1 :: Nil))(pos) & andR(pos)
  }

  def dBDG(p: Term, dim: Int): DependentPositionTactic =
    anon((pos: Position, sequent: Sequent) => dBDGInternal(p, dim)(pos, sequent))

  @Tactic(
    name = "dBDG",
    displayNameLong = Some("Bounded Diff Ghost"),
    displayLevel = DisplayLevelInternal,
    premises = "Γ |- [y'=g(x,y),x'=f(x) & Q]||y||^2 ≤ p(x) ;; Γ |- ⟨x'=f(x) & Q⟩P, Δ",
    conclusion = "Γ |- ⟨y'=g(x,y),x'=f(x) & Q⟩P, Δ",
  )
  def dBDG(p: Term): DependentPositionWithAppliedInputTactic =
    inputanon((pos: Position, sequent: Sequent) => dBDGInternal(p, 1)(pos, sequent))

  @Tactic(
    name = "dDDG",
    displayNameLong = Some("Differentially-bounded Diff Ghost"),
    displayLevel = DisplayLevelInternal,
    premises = "Γ |- [y'=g(x,y),x'=f(x) & Q](||y||^2)' <= L||y||+M ;; Γ |- ⟨x'=f(x) & Q⟩P, Δ",
    conclusion = "Γ |- ⟨y'=g(x,y),x'=f(x) & Q⟩P, Δ",
  )
  def dDDG(L: Term, M: Term): DependentPositionWithAppliedInputTactic =
    inputanon((pos: Position, sequent: Sequent) => dDDGInternal(L, M, 1)(pos, sequent))

  // Convenient wrappers for GEx
  def gEx(hints: List[Formula]): DependentPositionTactic = anon((pos: Position, seq: Sequent) =>
    odeReduce(strict = true, hints)(pos) & Idioms.?(cohideR(pos) & (byUScaught(Ax.TExge) | byUScaught(Ax.TExgt)) & done)
  )

  // todo: currently limited to one hint, but we actually need more than that!
  @Tactic(
    name = "gEx",
    displayNameLong = Some("Global Existence"),
    displayLevel = DisplayLevelAll,
    premises = "* (hint)",
    conclusion = "Γ |- ⟨x'=f(x),t'=1⟩t>s(), Δ",
  )
  def gEx(hint: Option[Formula]): DependentPositionWithAppliedInputTactic = inputanon((pos: Position) =>
    odeReduce(strict = true, hint.toList)(pos) & Idioms
      .?(cohideR(pos) & (byUScaught(Ax.TExge) | byUScaught(Ax.TExgt)) & done)
  )

  @Tactic(
    name = "dV",
    displayNameLong = Some("Differential Variant"),
    displayLevel = DisplayLevelAll,
    premises = " Γ |- ∃ε (ε>0 ∧ [x'=f(x)& Q∧¬P](P)'≳ε), Δ ;; Γ |- ∀s ⟨x'=f(x),t'=1 & Q⟩t≳s, Δ",
    conclusion = "Γ |- ⟨x'=f(x) & Q⟩P, Δ",
    inputs = "ε:Option[Term]",
  )
  def dV(eps: Option[Term]): DependentPositionWithAppliedInputTactic = inputanon((pos: Position, sequent: Sequent) => {
    // Check if the postcondition is an atomic inequality
    // Note: ill-formed applications are caught in the sub-tactics
    val atomic = sequent.sub(pos) match {
      case Some(Diamond(_, pred)) => pred.isInstanceOf[GreaterEqual] ||
        pred.isInstanceOf[Greater] ||
        pred.isInstanceOf[LessEqual] ||
        pred.isInstanceOf[Less]
      case _ => false
    }
    if (atomic) {
      eps match {
        case None => dVAuto(false)(pos)
        case Some(ee) => dV(ee)(pos)
      }
    } else {
      eps match {
        case None => semialgdVAuto(false)(pos)
        case Some(ee) => semialgdV(ee)(pos)
      }
    }
  })

}
