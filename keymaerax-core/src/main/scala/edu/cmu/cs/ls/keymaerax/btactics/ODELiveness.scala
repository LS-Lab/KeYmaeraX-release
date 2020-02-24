package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.ODEInvariance._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.infrastruct.DependencyAnalysis._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.tools.ext.Mathematica

/**
  * Implements ODE tactics for liveness.
  *
  * Created by yongkiat on 24 Feb 2020.
  */

object ODELiveness {

  private lazy val baseGEx = remember("<{gextimevar_'=1}> (gextimevar_ > p())".asFormula, solve(1) & QE & done)

  /** Computes the affine form for ODEs
    * @todo: this may also be extended to work with domain constraints
    * @param odes the ODEs to put into affine form
    * @return A (matrix of terms), b (list of terms), x (list of variables) such that x'=Ax+b
    */
  def affine_form (odes: DifferentialProgram) : (List[List[Term]], List[Term], List[Term]) = {

    val odels = DifferentialProduct.listify(odes).map {
      case AtomicODE(x,e) => (x,e)
      case _ => ??? //probably error
    }

    val lhs = odels.map(_._1)  // list of LHS y' of the ODEs
    val lhsvar = lhs.map(_.x.asInstanceOf[BaseVariable]) // list of y corresponding to the y'
    val rhs = odels.map( _._2) // list of RHS g(x,y) corresponding to the y'

    val toolCheck = ToolProvider.simplifierTool()

    val tool = toolCheck match {
      case None => None
      //@todo: this throws away the Z3 simplifier because it fails too much
      case Some(t) => {
        if (t.isInstanceOf[Mathematica]) Some(t)
        else None
      }
    }

    // the system matrix "A"
    val amat = rhs.map(t => simplifiedJacobian(t,lhsvar,tool))

    // ensure that "A" is actually linear
    val amatfree = amat.flatten.map( t => StaticSemantics.freeVars(t))
    if(amatfree.exists( s => lhsvar.exists(v => s.contains(v)))) {
      throw new IllegalArgumentException("Unable to automatically place ODE into affine form. Detected system matrix: " +  amat)
    }

    // Extracts the "affine part" by replacing all the LHS with 0 and then simplifying
    val rep0 = {e : Term => if (lhsvar.contains(e)) Some(Number(0):Term) else None}
    val rhssub = rhs.map(SubstitutionHelper.replacesFree(_)(rep0).asInstanceOf[Term])

    val bvec = rhssub.map(simpWithTool(tool,_))

    (amat,bvec,lhsvar)
  }

  // Helper that gets the appropriate VDG instance (already instantiated for the ghosts by renaming and friends)
  private def getVDGinst(ghostODEs:DifferentialProgram) : Provable = {

    val odels = DifferentialProduct.listify(ghostODEs).map {
      case AtomicODE(x,e) => (x,e)
      case _ => ??? //probably error
    }
    val ghostlist = DifferentialProduct.listify(ghostODEs)
    val dim = ghostlist.length
    val vdgraw = Provable.vectorialDG(dim)

    // @TODO: this very manually applies the uniform renaming part, since it's not automated elsewhere yet (?)
    // would also be much cleaner if one could access the renaming part more easily.
    val ghosts = (1 to dim).map( i => BaseVariable("y_", Some(i)))
    val lhs = odels.map(_._1.x)  // variables in the ODE
    val vdgren = (lhs zip ghosts).foldLeft(vdgraw)( (acc,bv) => acc(URename(bv._1,bv._2,semantic=true)) )

    // Now do the substitution part
    val oderen = vdgren.conclusion.succ(0).sub(PosInExpr(0::0::0::Nil)).get
    val unif = UnificationMatch.unifiable(oderen, DifferentialProduct(ghostODEs,DifferentialProgramConst("dummy_",Except(lhs)))).get

    //println("vdgraw ",vdgraw)
    //println("vdgren ",vdgren)
    vdgren(unif.usubst)
  }

  /** Repeated use of DE system */
  //todo: copied and tweaked from DifferentialTactics
  private lazy val DESystemCustom: DependentPositionTactic = new DependentPositionTactic("DE system step") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(f@Box(ODESystem(DifferentialProduct(AtomicODE(xp@DifferentialSymbol(x), t), c), h), p)) => {
          val ax = Provable.axioms("DE differential effect (system)")(URename("x_".asVariable,x,semantic=true))
          useAt(ElidingProvable(ax), PosInExpr(0::Nil))(pos) & DESystemCustom(pos)
        }
        case _ => skip
      }
    }
  }

  /** Repeated use of Dassignb */
  //todo: copied and tweaked from DifferentialTactics
  private lazy val DassignbCustom: DependentPositionTactic = new DependentPositionTactic("DE system step") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(Box(Assign(xp@DifferentialSymbol(x),f0), p)) => {
          val ax = Provable.axioms("[':=] differential assign")(URename("x_".asVariable,x,semantic=true))
          useAt(ElidingProvable(ax), PosInExpr(0::Nil))(pos) & DassignbCustom(pos)
        }
        case _ => skip
      }
    }
  }

  // returns the diff ghost instantiated and discharged to <ghost,c>P <-> <c> P
  private def proveVDGprecond(ghostODEs:DifferentialProgram) : ProvableSig = {

    //@note: throws IllegalArgumentException if affine form fails
    val (a,b,x) = affine_form(ghostODEs)

    //val ghosts = DifferentialProduct.listify(ghostODEs)
    val boundLem = ODEInvariance.affine_norm_bound(b.length)

    // the LHS 2*((A.x).x) + 2*(b.x)
    val lhs = boundLem.conclusion.succ(0).sub(PosInExpr(0::Nil)).get

    val lhsInst = Plus(
      Times(Number(2),dot_prod(matvec_prod(a,x),x)),
      Times(Number(2),dot_prod(b,x)))

    // Note: this should always unify
    val unif = UnificationMatch.unifiable(lhs, lhsInst).get.usubst
    val bound = boundLem(unif)

    // obtain the Lipschitz bounds by unification
    val lipsL = bound.conclusion.succ(0).sub(PosInExpr(1::0::0::Nil)).get
    // lipsM should always be 1 thanks to the way affine_norm_bound is proved
    val lipsM = bound.conclusion.succ(0).sub(PosInExpr(1::1::Nil)).get

    val vdgpre = getVDGinst(ghostODEs)

    val lipsLsub = vdgpre.conclusion.succ(0).sub(PosInExpr(0::1::1::0::0::Nil)).get
    val lipsMsub = vdgpre.conclusion.succ(0).sub(PosInExpr(0::1::1::1::Nil)).get

    val lipsLunif = UnificationMatch.unifiable(lipsLsub,lipsL).get.usubst
    val lipsMunif = UnificationMatch.unifiable(lipsMsub,lipsM).get.usubst
    val vdg = (vdgpre(lipsLunif))(lipsMunif)

    val goal = vdg.conclusion.succ(0).sub(PosInExpr(1::Nil)).get.asInstanceOf[Formula]
    val pre = vdg.conclusion.succ(0).sub(PosInExpr(0::Nil)).get.asInstanceOf[Formula]

    // matches g,h
    val unifpre1 = UnificationMatch(ineqLem.conclusion.succ(0).sub(PosInExpr(1::Nil)).get, pre).usubst
    // matches f
    val unifpre2 = UnificationMatch(ineqLem.conclusion.succ(0).sub(PosInExpr(0::1::1::0::Nil)).get, lhsInst).usubst
    val unifpre = ineqLem(unifpre1)(unifpre2)

    val pr = proveBy(goal,
      cutR(pre)(1)
      <(
        useAt(unifpre,PosInExpr(1::Nil))(1) & andR(1) <(
          DifferentialTactics.Dconstify(
            derive(1, PosInExpr(1 :: 1:: Nil)) &
            DESystemCustom(1) & G(1) & DassignbCustom(1) & QE
          )(1),
          G(1) & by(bound)
        ),
        by(ElidingProvable(vdg))
      ))

    pr
  }

  private val ineqLem1 = proveBy("f()=g()&f()<=h() ==>  g()<=h()".asSequent,QE)
  private val ineqLem = remember("[a_{|^@|};]f(||)=g(||) & [a_{|^@|};]f(||) <= h(||) -> [a_{|^@|};]g(||)<=h(||)".asFormula,
    implyR(1) & useAt("[] split", PosInExpr(1::Nil))(-1) & monb & byUS(ineqLem1)).fact

  private val diaflipLem = remember("(<a;>!p(||) <-> <b;>!p(||)) <-> ([a;]p(||) <-> [b;]p(||))".asFormula,
    useAt("<> diamond",PosInExpr(1::Nil))(1,0::0::Nil) &
      useAt("!! double negation",PosInExpr(0::Nil))(1,0::0::0::1::Nil) &
      useAt("<> diamond",PosInExpr(1::Nil))(1,0::1::Nil) &
      useAt("!! double negation",PosInExpr(0::Nil))(1,0::1::0::1::Nil) &
      prop
  ).fact

  /**
    * Given ODE, returns the global existence axiom <t'=1,x'=f(x)>t>p() (if it proves)
    * @param ode
    * @return (optional) ProvableSig proving the global existence axiom, None if failed
    */
  def deriveGlobalExistence(ode: DifferentialProgram ) : Option[ProvableSig] = {

    val timevar = "gextimevar_".asVariable
    val rhs = "p()".asTerm
    val post = Greater(timevar,rhs)
    val timeode = "gextimevar_'=1".asDifferentialProgram

    val odels = DifferentialProduct.listify(ode).map{
      case ve@AtomicODE(x,e) => (x.x,ve)
      case _ => return None
    }.toMap

    val adjs = analyseODEVars(ODESystem(ode,True), ignoreTest = true, checklinear = false)
    val ls = scc(adjs).map(_.toList)

    val odeGroups = ls.map( vs => {
      val odes = vs.map(vv => odels(vv))
      odes.tail.foldLeft(odes.head:DifferentialProgram)( (p,r) => DifferentialProduct(p,r))
    }
    )

    var pr = baseGEx.fact
    var curode = timeode

    for(odeG <- odeGroups) {

      curode = DifferentialProduct(odeG,curode)

      val vdg = try proveVDGprecond(odeG) catch {
        case e: IllegalArgumentException => return None
      }

      pr = proveBy(Diamond(ODESystem(curode,True), post),
        cutR(pr.conclusion.succ(0))(1) <( by(pr),
          implyR(1) &
            useAt("<> diamond",PosInExpr(1::Nil))(1) &
            useAt("<> diamond",PosInExpr(1::Nil))(-1) &
            notL(-1) & notR(1) & implyRi & equivifyR(1) &
            commuteEquivR(1) &
            byUS(vdg)
        )
      )

      //println("pr: ",pr)
      if(!pr.isProved)
        return None
    }

    val resode = DifferentialProduct(timeode,ode)
    val goal = ls.reverse.flatMap(_.toList)
    val sortTac = AxiomaticODESolver.selectionSort(True, Not(post), resode, goal:+timevar, AntePosition(1))

    val res = proveBy(Diamond(ODESystem(resode,True), post),
      useAt("<> diamond", PosInExpr(1::Nil))(1) & notR(1) & sortTac &
        useAt("[] box", PosInExpr(1::Nil))(-1) & notL(-1) &
        useAt("!! double negation")(1, 1::Nil) & byUS(pr)
    )

    Some(res)
  }

}