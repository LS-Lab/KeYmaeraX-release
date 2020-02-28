package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.ODEInvariance._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3.ineqNormalize
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.infrastruct.DependencyAnalysis._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.tools.ext.Mathematica

import scala.collection.immutable
import scala.collection.immutable.Nil
import scala.collection.mutable.ListBuffer

/**
  * Implements ODE tactics for liveness.
  *
  * Created by yongkiat on 24 Feb 2020.
  */

object ODELiveness {

  private val namespace = "odeliveness"

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

  // helper that simplifies the precondition of vdg
  private def simplifyPre(pr : ProvableSig, bnd : Term) : ProvableSig = {
    val seq = pr.conclusion
    val left = seq.succ(0).sub(PosInExpr(0::Nil)).get.asInstanceOf[Formula]
    val right = seq.succ(0).sub(PosInExpr(1::Nil)).get.asInstanceOf[Formula]

    val leftnew = left.replaceAt(PosInExpr(1::0::Nil), bnd)

    proveBy( Imply(leftnew,right),
      implyR(1) & cutR(left)(1) <(
        implyRi & useAt(ineqLem,PosInExpr(1::Nil))(1) &
          DifferentialTactics.Dconstify(
            derive(1, PosInExpr(1 :: 1:: Nil)) &
              DESystemCustom(1) & G(1) & DassignbCustom(1) & QE
          )(1)
        ,
        cohideR(1) & by(pr)
      ))
  }

  // Helper that gets the appropriate VDG instance (already instantiated for the ghosts by renaming and friends)
  def getVDGinst(ghostODEs:DifferentialProgram) : (ProvableSig, ProvableSig) = {

    val odels = DifferentialProduct.listify(ghostODEs).map {
      case AtomicODE(x,e) => (x,e)
      case _ => throw new IllegalArgumentException("list of ghost ODEs should all be atomic, found: "+ghostODEs)
    }
    val ghostlist = DifferentialProduct.listify(ghostODEs)
    val dim = ghostlist.length
    val (vdgrawimply,vdgrawylpmi) = Provable.vectorialDG(dim)

    // @TODO: this very manually applies the uniform renaming part, since it's not automated elsewhere yet (?)
    // would also be much cleaner if one could access the renaming part more easily.
    val ghosts = (1 to dim).map( i => BaseVariable("y_", Some(i)))
    val lhs = odels.map(_._1.x)  // variables in the ODE
    val vdgimplyren = (lhs zip ghosts).foldLeft(vdgrawimply)( (acc,bv) => acc(URename(bv._1,bv._2,semantic=true)) )
    val vdgylpmiren = (lhs zip ghosts).foldLeft(vdgrawylpmi)( (acc,bv) => acc(URename(bv._1,bv._2,semantic=true)) )

    // Now do the substitution part
    val odeimplyren = vdgimplyren.conclusion.succ(0).sub(PosInExpr(0::0::0::Nil)).get
    val unif = UnificationMatch.unifiable(odeimplyren, DifferentialProduct(ghostODEs,DifferentialProgramConst("dummy_",Except(lhs)))).get

    val resimply = vdgimplyren(unif.usubst)
    val resylpmi = vdgylpmiren(unif.usubst)

    // (||y||^2)' = 2y.g(x,yy)
    val bnd = Times(Number(2), odels.map(ve => Times(ve._1.x,ve._2)).reduce(Plus.apply))

    (simplifyPre(ElidingProvable(resimply),bnd), ElidingProvable(resylpmi))
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

  // returns the diff ghost instantiated and discharged
  private def affineVDGprecond(ghostODEs:DifferentialProgram) : ProvableSig = {

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

    val vdgpre = getVDGinst(ghostODEs)._1

    val lipsLsub = vdgpre.conclusion.succ(0).sub(PosInExpr(0::1::1::0::0::Nil)).get
    val lipsMsub = vdgpre.conclusion.succ(0).sub(PosInExpr(0::1::1::1::Nil)).get

    val lipsLunif = UnificationMatch.unifiable(lipsLsub,lipsL).get.usubst
    val lipsMunif = UnificationMatch.unifiable(lipsMsub,lipsM).get.usubst
    val vdg = (vdgpre(lipsLunif))(lipsMunif)

    val goal = vdg.conclusion.succ(0).sub(PosInExpr(1::Nil)).get.asInstanceOf[Formula]
    val pre = vdg.conclusion.succ(0).sub(PosInExpr(0::Nil)).get.asInstanceOf[Formula]

    val pr = proveBy(goal,
      cutR(pre)(1)
      <(
        G(1) & cutR(bound.conclusion.succ(0))(1) <(
          by(bound),
          useAt(ineqLem1,PosInExpr(1::Nil))(1) & QE
        ) ,
        by(vdg)
      ))

    pr
  }

  private lazy val ineqLem1 = remember("f_()=g_() -> f_()<=h_() ->  g_()<=h_()".asFormula,QE, namespace)
  private lazy val ineqLem = remember("[a_{|^@|};]f(||)=g(||) -> [a_{|^@|};]f(||) <= h(||) -> [a_{|^@|};]g(||)<=h(||)".asFormula,
    implyR(1) & implyR(1) & andLi & useAt("[] split", PosInExpr(1::Nil))(-1) & monb & andL(-1) & implyRi()(AntePosition(2),SuccPosition(1)) & implyRi & byUS(ineqLem1), namespace)

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

    val adjs = analyseODEVars(ODESystem(ode,True), ignoreTest = true, checkLinear = false)

    val ls = scc(adjs).map(_.toList)

    val odeGroups = ls.map( vs => {
      val odes = vs.map(vv => odels(vv))
      odes.tail.foldLeft(odes.head:DifferentialProgram)( (p,r) => DifferentialProduct(p,r))
    }
    )

    var pr = baseGExgt.fact //baseGExge.fact for the >= version
    var curode = timeode

    for(odeG <- odeGroups) {

      curode = DifferentialProduct(odeG,curode)

      val vdg = try affineVDGprecond(odeG) catch {
        case e: IllegalArgumentException => return None
      }

      val vdgflip = flipModality(vdg)
      pr = useFor(vdgflip,PosInExpr(0::Nil))(Position(1))(pr)
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

  //Helper to remove a nonlinear ODE
  private def removeODENonLin(ode : DifferentialProgram, strict:Boolean, cont:BelleExpr) : DependentPositionTactic = "ANON" by ((pos:Position,seq:Sequent) => {

    val vdgpre = getVDGinst(ode)._1
    val vdgsubst = UnificationMatch(vdgpre.conclusion.succ(0).sub(PosInExpr(1::0::Nil)).get, seq.sub(pos).get).usubst

    // the concrete vdg instance
    val vdg = vdgpre(vdgsubst)

    val vdgasm = vdg.conclusion.succ(0).sub(PosInExpr(0::Nil)).get

    // check for an assumption in the context
    val ind = seq.ante.indexWhere( f => UnificationMatch.unifiable(vdgasm,f).isDefined )

    if(ind == -1) {
      if (strict) throw new BelleThrowable("odeReduce failed to autoremove: " + ode + ". Try to add an assumption of this form to the antecedents: " + vdgasm)
      else skip
    }
    else {
      val unif = UnificationMatch(vdgasm,seq.ante(ind)).usubst
      val finalrw = vdg(unif)
      val concl = finalrw.conclusion.succ(0).sub(PosInExpr(1::1::Nil)).get.asInstanceOf[Formula]

      cutL(concl)(pos) <( cont,
        cohideOnlyR('Rlast) & useAt(finalrw,PosInExpr(1::Nil))(1) & closeId
      )
    }
  })

  private def removeODEs(ls : List[DifferentialProgram], pos:Position, strict:Boolean) : BelleExpr = {

    if(ls.isEmpty) return skip

    val vdg = try
      affineVDGprecond(ls.head)
    catch {
      case e : IllegalArgumentException =>
        return removeODENonLin(ls.head,strict,removeODEs(ls.tail,pos, strict))(pos)
    }

    useAt(vdg,PosInExpr(0::Nil))(pos) & removeODEs(ls.tail,pos, strict)
  }

  /** Applied to a top-level position containing a succedent diamond, this tactic removes irrelevant ODEs
    *
    * @param strict whether to throw an error when it meets a nonlinear ODE that can't be reduced
    * @return reduces away all irrelevant ODEs
    */
  def odeReduce(strict: Boolean = true) : DependentPositionTactic = "odeReduce" by ((pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "odeReduce is only applicable at a top-level succedent")

    val (sys,post) = seq.sub(pos) match {
      case Some(Diamond(sys:ODESystem,post)) => (sys,post)
      case _ => throw new BelleThrowable("odeReduce only applicable to diamond ODE in succedent")
    }

    val ode = sys.ode

    val odels = DifferentialProduct.listify(ode).map{
      case ve@AtomicODE(x,e) => (x.x,ve)
      case _ => throw new BelleThrowable("odeReduce only applicable to concrete ODEs")
    }.toMap

    // The set of variables transitively depended on by the postcondition and domain constraint
    // These cannot be removed!
    val fvs = StaticSemantics.freeVars(And(sys.constraint,post)).toSet
    val basefvs = fvs.filter(v => v.isInstanceOf[BaseVariable]).map(v =>v.asInstanceOf[BaseVariable])
    val unremovable = analyseODE(ODESystem(ode,True), basefvs , ignoreTest = true, checkLinear = false)._1.toList

    val adjs = analyseODEVars(ODESystem(ode,True), ignoreTest = true, checkLinear = false)
    // The remaining removable ODEs
    val ls = scc(adjs).map(_.toList)

    if(ls.length <= 1)
      // unable to do anything for a single group of ODE
      skip

    else {
      val lsr = ls.filter(vs => vs.intersect(unremovable).isEmpty)
      val lsu = ls.filter(vs => vs.intersect(unremovable).nonEmpty)

      // println(ls)

      //We will remove the ODEs in ls from back to front
      val odeGroups = lsr.map(vs => {
        val odes = vs.map(vv => odels(vv))
        odes.tail.foldLeft(odes.head: DifferentialProgram)((p, r) => DifferentialProduct(p, r))
      }
      )

      val goal = lsr.reverse.flatMap(_.toList) ++ lsu.flatMap(_.toList)
      val sortTac = AxiomaticODESolver.selectionSort(sys.constraint, Not(post), ode, goal, AntePosition(seq.ante.length + 1))

      val red = removeODEs(odeGroups.reverse, AntePosition(seq.ante.length + 1), strict)
      //    val resode = DifferentialProduct(timeode,ode)
      //    val goal = ls.reverse.flatMap(_.toList)
      //    val sortTac = AxiomaticODESolver.selectionSort(True, Not(post), resode, goal:+timevar, AntePosition(1))

      //Moves diamonds into anteposition and sorts
      useAt("<> diamond", PosInExpr(1 :: Nil))(pos) & notR(pos) & sortTac &
        // Apply the reduction
        red &
        //Moves back into diamond
        useAt("[] box", PosInExpr(1 :: Nil))(AntePosition(seq.ante.length + 1)) & notL('Llast) &
        useAt("!! double negation")(seq.succ.length, 1 :: Nil) &
        ProofRuleTactics.exchangeR(Position(seq.succ.length),pos)
    }
  })

  // Tries to make the second ODE line up with the first one by deleting and reordering ODEs
  // dom is the domain of the second ODE and post is the postcond of the first
  private def compatODE(ode1: DifferentialProgram, ode2: DifferentialProgram, dom: Formula, post: Formula) : Option[BelleExpr] = {
    val ode1ls = DifferentialProduct.listify(ode1)
    val ode2ls = DifferentialProduct.listify(ode2)

    //Common case: both ODEs are the same
    if(ode1ls==ode2ls) {
      Some(skip)
    }
    //ODE1 must be a subset of ODE2
    else if(ode1ls.diff(ode2ls).nonEmpty) None
    else {
      // Ignore non atomic ODEs
      if(!ode1ls.forall(_.isInstanceOf[AtomicODE]) && !ode2ls.forall(_.isInstanceOf[AtomicODE]) )
        return None
      // ODE2 can have some extras, which we can get rid of
      val extra = ode2ls.diff(ode1ls)

      val extravars = extra.map(_.asInstanceOf[AtomicODE].xp.x)

      if(!StaticSemantics.freeVars(And(dom,post)).intersect(extravars.toSet).isEmpty)
        return None

      val vars = extravars ++ (ode1ls.map(_.asInstanceOf[AtomicODE].xp.x))

      // The goal is to sort ODE2 into extra++ODE1
      // Then add extra to ODE1
      Some(
        AxiomaticODESolver.selectionSort(dom, post, ode2, vars, SuccPosition(1))
          &
        (
          if(extra.isEmpty) skip
          else vDG(extra.reduce(DifferentialProduct.apply))(-1)
        )
      )

    }
  }

  /** Adds compatible box modalities from the assumptions to the domain constraint
    * [x'=f(x)&A]B is compatible for [x'=f(x)&Q]P
    * if A implies Q
    *
    * For compatible assumptions, the rule adds them by diff cut:
    *
    * G, [x'=f(x)&A]B |- [x'=f(x)&Q&B]P
    * ---
    * G, [x'=f(x)&A]B |- [x'=f(x)&Q]P
    */
  def compatCuts : DependentPositionTactic = "compatCuts" by ((pos:Position, seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "compatCuts is only applicable at a top-level succedent")

    val (tarsys,tarpost) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,post)) => (sys,post)
      case _ => throw new BelleThrowable("compatCuts only applicable to box ODE in succedent")
    }

    // Loop through compatible assumptions and track the effect of DC
    var curdom = tarsys.constraint
    var curdomls = FormulaTools.conjuncts(curdom)

    var ls = new ListBuffer[(Formula, ProvableSig, Formula, Int, BelleExpr)] ()

    for (i <- seq.ante.indices) {
      val asm = seq.ante(i)
      asm match {
        case Box(asmsys:ODESystem,asmpost) =>
          if(!curdomls.contains(asmpost)) {
            compatODE(asmsys.ode,tarsys.ode, curdom, asmpost) match {
              case None => ()
              case Some(tac) => {
                val pr = proveBy(Sequent(immutable.IndexedSeq(curdom), immutable.IndexedSeq(asmsys.constraint)), Idioms.?(QE)) //todo: timeout?

                if (pr.isProved) {
                  ls += ((asmsys.constraint, pr, asmpost, i, tac))
                  curdom = And(curdom, asmpost)
                  curdomls = curdomls :+ asmpost
                }
                else ()
              }
            }
          }
        case _ => ()
      }
    }

    //println("compatible asms: ", ls)

    ls.foldLeft(skip) (
      (in,fp) => {
        val (dom,pr,f,i,tac) = (fp._1,fp._2,fp._3,fp._4,fp._5)
        in & dC(f)(pos) <(
          skip,
          cohideOnlyL(AntePosition(i+1)) & cohideOnlyR(pos) &
            //DebuggingTactics.print("before") &
            tac &
            //DebuggingTactics.print("after") &
            dR(dom)(1) <( closeId,
            DifferentialTactics.diffWeakenG(1) & implyR(1) & by(pr) )
        )
      }
    )
  })

  /** Implements K<&> rule
    * Note: uses auto cuts for the later premise
    *
    * G |- <ODE & Q> R
    * G |- [ODE & Q & !P] !R
    * ---- (kDomD)
    * G |- <ODE & Q> P
    *
    * @param target the formula R to refine the postcondition
    * @return two premises, as shown above when applied to a top-level succedent diamond
    */
  def kDomainDiamond(target: Formula): DependentPositionTactic = "kDomD" byWithInput (target,(pos: Position, seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "kDomD is only applicable at a top-level succedent")

    val (sys,post) = seq.sub(pos) match {
      case Some(Diamond(sys:ODESystem,post)) => (sys,post)
      case _ => throw new BelleThrowable("kDomD only applicable to diamond ODE in succedent")
    }

    val newfml = Diamond(sys,target)

    cutR(newfml)(pos) <(
      skip,
      useAt("K<&>",PosInExpr(1::Nil))(pos) & compatCuts(pos)
    )
  })

  /** Implements DR<.> rule
    * Note: uses auto cuts for the later premise
    *
    * G |- <ODE & R> P
    * G |- [ODE & R] Q
    * ---- (kDomD)
    * G |- <ODE & Q> P
    *
    * @param target the formula R to refine the domain constraint
    * @return two premises, as shown above when applied to a top-level succedent diamond
    */
  def dDR(target: Formula): DependentPositionTactic = "dDR" byWithInput (target,(pos: Position, seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "dDR is only applicable at a top-level succedent")

    val (sys,post) = seq.sub(pos) match {
      case Some(Diamond(sys:ODESystem,post)) => (sys,post)
      case _ => throw new BelleThrowable("dDR only applicable to diamond ODE in succedent")
    }

    val newfml = Diamond(ODESystem(sys.ode,target),post)

    cutR(newfml)(pos) <(
      skip,
      useAt("DR<> differential refine",PosInExpr(1::Nil))(pos) & compatCuts(pos)
    )
  })

  /** Implements vDG rule that adds ghosts to an ODE on the left or right, in either modality
    * For boxes on the right and diamonds on the left, the ODE must be affine
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
    * @param ghost the ODEs to ghost in
    * @return the sequent with ghosts added in requested position
    */
  def vDG(ghost: DifferentialProgram): DependentPositionTactic = "vDG" byWithInput (ghost,(pos: Position, seq:Sequent) => {
    require(pos.isTopLevel, "vDG is only applicable at a top-level position")

    val (sys,post,isBox) = seq.sub(pos) match {
      case Some(Diamond(sys:ODESystem,post)) => (sys,post,false)
      case Some(Box(sys:ODESystem,post)) => (sys,post,true)
      case _ => throw new BelleThrowable("vDG only applicable to box ODE in antecedents or diamond ODE in succedents")
    }

    //@todo: Check that ghosts are sufficiently fresh and return a nice error

    if(pos.isSucc ^ isBox) {
      val vdg = getVDGinst(ghost)._2
      if(isBox) useAt(vdg,PosInExpr(0::Nil))(pos)
      else //diamond in succedent
        useAt(flipModality(vdg),PosInExpr(1::Nil))(pos)
    }
    else {
      val vdg = affineVDGprecond(ghost)
      if(isBox) useAt(vdg,PosInExpr(1::Nil))(pos)
      else //diamond in antecedent
        useAt(flipModality(vdg),PosInExpr(0::Nil))(pos)
    }
  })

  // Flips a proved [a]p(||) -> [b]p(||) into <b>p(||) -> <a>p(||) or vice versa, possibly with bananas for p(||)
  private def flipModality(pr:ProvableSig) : ProvableSig = {

    val fml = pr.conclusion.succ(0)

    fml match {
      case Imply(Box(proga,post),Box(progb,post2)) if post==post2 && post.isInstanceOf[UnitPredicational] => {
        proveBy(Imply(Diamond(progb,post),Diamond(proga,post)),
          implyR(1) &
            useAt("<> diamond", PosInExpr(1 :: Nil))(1) & notR(1) &
            useAt("<> diamond", PosInExpr(1 :: Nil))(-1) & notL(-1) &
          implyRi & byUS(pr)
        )
      }
      case Imply(Diamond(proga,post),Diamond(progb,post2)) if post==post2 && post.isInstanceOf[UnitPredicational] => {
        proveBy(Imply(Box(progb,post),Box(proga,post)),
          implyR(1) &
            useAt("[] box", PosInExpr(1 :: Nil))(1) & notR(1) &
            useAt("[] box", PosInExpr(1 :: Nil))(-1) & notL(-1) &
            implyRi & byUS(pr)
        )
      }
      case _ => ???
    }
  }

  /** Implements dV rule for atomic postconditions
    * The bottom two premises are auto-closed because of the need to Dconstify
    * The first one is partially auto-closed if odeReduce is able to prove global existence
    * e.g. (similarly for dV >),
    *
    * Note: autonormalizes to >= and > (but provided e() must be for the normalized shape!)
    *
    * G, t=0 |- <t'=1, ODE & Q> t > const
    * G, t=0 |- e() > 0
    * G, t=0 |- [t'=1, ODE & Q & p-q < 0] p'-q' >= e () (this uses compatible cuts )
    * ---- (dV >=)
    * G |- <ODE & Q> p >= q
    *
    * Note that domain constraint Q is kept around!
    *
    * @param bnd the lower bound on derivatives
    * @return closes (or partially so)
    */
  def dV(bnd: Term): DependentPositionTactic = "dV" byWithInput (bnd,(pos: Position, seq:Sequent) => {
    require(pos.isTopLevel, "dV is only applicable at a top-level succedent")

    val (sys,post) = seq.sub(pos) match {
      case Some(Diamond(sys:ODESystem,post)) => (sys,post)
      case _ => throw new BelleThrowable("dV only applicable to diamond ODE in succedent")
    }

    val (property, propt) = ineqNormalize(post)

    val starter = propt match {
      case None => skip
      case Some(pr) => useAt(pr)(pos ++ PosInExpr(1::Nil))
    }

    //support for old
    val timevar = TacticHelper.freshNamedSymbol("timevar_".asVariable, seq)

    val timer = AtomicODE(DifferentialSymbol(timevar),Number(1))

    // Introduces the time variable in a mildly gross way so that it is set to 0 initially
    val timetac =
      cut(Exists(List(timevar), Equal(timevar,Number(0)))) <( existsL('Llast), cohideR('Rlast) & QE) &
      vDG(timer)(pos)

    val p = property.sub(PosInExpr(0::Nil)).get.asInstanceOf[Term]
    val oldp = TacticHelper.freshNamedSymbol("oldp".asVariable, seq)

    val unifODE = UnificationMatch("{c &q_(||)}".asProgram, sys).usubst
    val unify = UnificationMatch("p(||) + e()".asTerm, Plus(oldp,bnd)).usubst

    val ax = property match {
      case Greater(_, _) => DVgt.fact(unifODE) (unify)
      case GreaterEqual(_, _) => DVgeq.fact(unifODE) (unify)
      case _ => ??? //impossible
    }
    val axren = ax(URename(timevar,"t".asVariable,semantic=true))

    val ex = property match {
      case Greater(_, _) => baseGExgt.fact
      case GreaterEqual(_, _) => baseGExge.fact
      case _ => ??? //impossible
    }

    starter & timetac &
    discreteGhost(p, Some(oldp))(pos) &
    useAt(axren,PosInExpr(1::Nil))(pos) &
    andR(pos) <(
      andR(pos) <(
      ToolTactics.hideNonFOL & QE, //G |- e() > 0
      odeReduce(strict = false)(pos) & Idioms.?(cohideR(pos) & byUS(ex))), // existence
      compatCuts(pos) & dI('full)(pos)  // derivative lower bound
    )
  })

  // Semialgebraic dV
  def semialgdV(bnd: Term): DependentPositionTactic = "semialgdV" byWithInput (bnd,(pos: Position, seq:Sequent) => {
    require(pos.isTopLevel, "dV is only applicable at a top-level succedent")

    val (sys,post) = seq.sub(pos) match {
      case Some(Diamond(sys:ODESystem,post)) => (sys,post)
      case _ => throw new BelleThrowable("dV only applicable to diamond ODE in succedent")
    }

    val (property, propt) = SimplifierV3.semiAlgNormalize(post)

    val starter = propt match {
      case None => skip
      case Some(pr) => useAt(pr)(pos ++ PosInExpr(1::Nil))
    }

    //support for old
    val timevar = TacticHelper.freshNamedSymbol("timevar_".asVariable, seq)

    val timer = AtomicODE(DifferentialSymbol(timevar),Number(1))

    // Introduces the time variable in a mildly gross way so that it is set to 0 initially
    val timetac =
      cut(Exists(List(timevar), Equal(timevar,Number(0)))) <( existsL('Llast), cohideR('Rlast) & QE) &
        vDG(timer)(pos)

    //Symbolic lower bound
    val oldp = TacticHelper.freshNamedSymbol("oldp".asVariable, seq)

    val oldpbound = Greater(Plus(oldp,Times(bnd, timevar)), Number(0))

    def mkFml(fml: Formula) : Formula = {
      fml match {
        case Greater(p , _) => GreaterEqual(p, Plus(oldp,Times(bnd, timevar)))
        case GreaterEqual(p , _) => GreaterEqual(p, Plus(oldp,Times(bnd, timevar)))
        case And(l,r) => And(mkFml(l),mkFml(r))
        case Or(l,r) => Or(mkFml(l),mkFml(r))
        case _ => ??? //impossible thanks to normalization
      }
    }

    val inv = mkFml(property)

    starter & timetac &
    cut(Exists(List(oldp),inv)) <(
      existsL('Llast),
      cohideR('Rlast) & QE //this should be a trivial QE question
    ) &
    kDomainDiamond(oldpbound)(pos) <(
      useAt(exRWgt,PosInExpr(1::Nil))(pos)& andR(pos) <(
        ToolTactics.hideNonFOL & QE,
        odeReduce(strict = false)(pos) & Idioms.?(cohideR(pos) & byUS(baseGExgt)), // existence
      ),
      dC(inv)(pos) <(
        DW(pos) & G(pos) & ToolTactics.hideNonFOL & QE, //can be proved manually
        sAIclosedPlus()(1) //ODE(1) does a boxand split, which is specifically a bad idea here
      )

    )

  })

  /** some of these should morally be in DerivedAxioms but have weird dependencies */
  private lazy val baseGExge = remember("<{gextimevar_'=1}> (gextimevar_ >= p())".asFormula, solve(1) & QE & done, namespace)
  private lazy val baseGExgt = remember("<{gextimevar_'=1}> (gextimevar_ > p())".asFormula, solve(1) & QE & done, namespace)

  private lazy val exRWgt = remember("e() > 0 & <{t'=1, c &q_(||)}> t > -p(||)/e() -> <{t'=1, c &q_(||)}> p(||) + e() * t > 0".asFormula,
    implyR(1) & andL(-1) &
      cutR("<{t'=1,c&q_(||)}>(t>-p(||)/e() & e() > 0)".asFormula)(1) <(
        implyRi()(AntePosition(2),SuccPosition(1)) & useAt("K<&>",PosInExpr(1::Nil))(1) &
          cutR("[{t'=1,c&(q_(||)&!(t>-p(||)/e()&e()>0)) & e() > 0}](!t>-p(||)/e())".asFormula)(1)<(
            DW(1) & G(1) & prop,
            equivifyR(1) & commuteEquivR(1) &
              useAt("DC differential cut",PosInExpr(1::Nil))(1) & V(1) & closeId
          ) ,
        cohideR(1) & implyR(1) & mond & byUS(proveBy("t>-p()/e()&e()>0 ==> p()+e()*t>0".asSequent,QE))
      ),
    namespace
  )

  private lazy val exRWge = remember("e() > 0 & <{t'=1, c &q_(||)}> t >= -p(||)/e() -> <{t'=1, c &q_(||)}> p(||) + e() * t >= 0".asFormula,
    implyR(1) & andL(-1) &
      cutR("<{t'=1,c&q_(||)}>(t>=-p(||)/e() & e() > 0)".asFormula)(1) <(
        implyRi()(AntePosition(2),SuccPosition(1)) & useAt("K<&>",PosInExpr(1::Nil))(1) &
          cutR("[{t'=1,c&(q_(||)&!(t>=-p(||)/e()&e()>0)) & e() > 0}](!t>=-p(||)/e())".asFormula)(1)<(
            DW(1) & G(1) & prop,
            equivifyR(1) & commuteEquivR(1) &
              useAt("DC differential cut",PosInExpr(1::Nil))(1) & V(1) & closeId
          ) ,
        cohideR(1) & implyR(1) & mond & byUS(proveBy("t>=-p()/e()&e()>0 ==> p()+e()*t>=0".asSequent,QE))
      ),
    namespace
  )

  private lazy val DVgeq = remember(
    "(e() > 0 & <{t'=1, c &q_(||)}> t >= -p(||)/e()) & [{t'=1, c & q_(||) & f_(||) < 0}] f_(||) >= p(||) + e() * t -> <{t'=1, c & q_(||)}> f_(||) >= 0".asFormula,
    implyR(1) & andL(-1) & useAt(exRWge.fact,PosInExpr(0::Nil))(-1) & implyRi &
    useAt("K<&>",PosInExpr(1::Nil))(1) &
    cutR("[{t'=1,c&(q_(||)&!f_(||)>=0)&f_(||) >= p(||) + e() * t}](!p(||) + e()* t >= 0)".asFormula)(1)<(
      DW(1) & G(1) & prop & hideL(-2) & byUS(proveBy("f_()>=p()+e()*t, p()+e()*t>=0  ==>  f_()>=0".asSequent,QE)),
      equivifyR(1) & commuteEquivR(1) &
        useAt("DC differential cut",PosInExpr(1::Nil))(1) &
        useAt("! >=",PosInExpr(0::Nil))(1,0::1::1::Nil) & closeId
    ), namespace
  )

  private lazy val DVgt = remember(
    "(e() > 0 & <{t'=1, c &q_(||)}> t > -p(||)/e()) & [{t'=1, c & q_(||) & f_(||) <= 0}] f_(||) >= p(||) + e() * t -> <{t'=1, c & q_(||)}> f_(||) > 0".asFormula,
    implyR(1) & andL(-1) & useAt(exRWgt.fact,PosInExpr(0::Nil))(-1) & implyRi &
    useAt("K<&>",PosInExpr(1::Nil))(1) &
    cutR("[{t'=1,c&(q_(||)&!f_(||)>0)&f_(||) >= p(||) + e() * t}](!p(||) + e()* t > 0)".asFormula)(1)<(
      DW(1) & G(1) & prop & hideL(-2) & byUS(proveBy("f_()>=p()+e()*t, p()+e()*t>0  ==>  f_()>0".asSequent,QE)),
      equivifyR(1) & commuteEquivR(1) &
        useAt("DC differential cut",PosInExpr(1::Nil))(1) &
        useAt("! >",PosInExpr(0::Nil))(1,0::1::1::Nil) & closeId
    ), namespace
  )

  /** Implements higher dV series rule for atomic postconditions with less automation
    * Given a series a_0, a_1, ... , a_n :
    *
    * G |- [t'=1, ODE&Q & p<0] p >= a_0 + a_1 t + a_2 t^2 + ... + a_n t^n
    * G |- <t'=1, ODE & Q> a_0 + a_1 t + a_2 t^2 + ... + a_n t^n > 0
    * ---- (higherdV >=)
    * G |- <ODE & Q> p >= 0
    *
    * Note that domain constraint Q is kept around!
    *
    * @param bnds the lower bound on derivatives
    * @return two subgoals, shown above
    */
  def higherdV(bnds: List[Term]): DependentPositionTactic = "higherdV" byWithInput (bnds,(pos: Position, seq:Sequent) => {
    require(pos.isTopLevel, "Higher dV is only applicable at a top-level succedent")

    val (sys,post) = seq.sub(pos) match {
      case Some(Diamond(sys:ODESystem,post)) => (sys,post)
      case _ => throw new BelleThrowable("Higher dV only applicable to diamond ODE in succedent")
    }

    val (property, propt) = ineqNormalize(post)

    val starter = propt match {
      case None => skip
      case Some(pr) => useAt(pr)(pos ++ PosInExpr(1::Nil))
    }

    //support for old
    val timevar = TacticHelper.freshNamedSymbol("timevar_".asVariable, seq)
    val timer = AtomicODE(DifferentialSymbol(timevar),Number(1))

    // Introduces the time variable in a mildly gross way so that it is set to 0 initially
    val timetac =
      cut(Exists(List(timevar), Equal(timevar,Number(0)))) <( existsL('Llast), cohideR('Rlast) & QE) &
        vDG(timer)(pos)

    val p = property.sub(PosInExpr(0::Nil)).get.asInstanceOf[Term]

    //todo: directly support old(.) in term list instead of baking it in
    //should coeff be baked in or not?
    val coeff = TacticHelper.freshNamedSymbol("coeff".asVariable, seq)
    val coefflist = (0 to bnds.length-1).map( i => Variable(coeff.name+i))
    val coefftac = (bnds zip coefflist).map( bc => discreteGhost(bc._1,Some(bc._2))(pos) : BelleExpr).reduce(_ & _)

    val series = coefflist.tail.zipWithIndex.foldLeft(coefflist.head:Term) { (h,fe) => Plus(h,Times(fe._1, Power(timevar, Number(fe._2+1)))) }

    val ex = property match {
      case Greater(_, _) => baseGExgt.fact
      case GreaterEqual(_, _) => baseGExge.fact
      case _ => ??? //impossible
    }

    starter & timetac & coefftac &
    kDomainDiamond(property.asInstanceOf[ComparisonFormula].reapply(series,Number(0)))(pos) <(
      odeReduce(strict=false)(pos) & Idioms.?(solve(pos) & QE),
      dC(GreaterEqual(p,series))(pos) <(
        DW(pos) & G(pos) & QE // might as well have usubst here
        ,
        skip
      )
    )
//      discreteGhost(p, Some(oldp))(pos) &
//      useAt(axren,PosInExpr(1::Nil))(pos) &
//      andR(pos) < (
//        ToolTactics.hideNonFOL & QE //G |- e() > 0
//        ,
//        andR(pos) <(
//          odeReduce(strict = false)(pos) & Idioms.?(cohideR(pos) & byUS(ex)), // existence
//          compatCuts(pos) & dI('full)(pos)  // derivative lower bound
//        )
//      )
  })

  /** Saves a (negated) box version of the liveness postcondition.
    * This is a helpful pattern because of compat cuts
    *
    * G, [ODE & Q]!P |- <ODE & Q> P
    * ---- (saveBox)
    * G |- <ODE & Q> P
    */
  def saveBox : DependentPositionTactic = "saveBox" by ((pos:Position, seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "saveBox is only applicable at a top-level succedent")

    val (tarsys, tarpost) = seq.sub(pos) match {
      case Some(Diamond(sys: ODESystem, post)) => (sys, post)
      case _ => throw new BelleThrowable("saveBox only applicable to diamond ODE in succedent")
    }

    cut(Box(tarsys,Not(tarpost))) <(
      skip,
      useAt("<> diamond",PosInExpr(1::Nil))(pos) & notR(pos) & closeId
    )
  })

}
