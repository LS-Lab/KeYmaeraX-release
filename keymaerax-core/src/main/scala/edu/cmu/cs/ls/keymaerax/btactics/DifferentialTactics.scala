package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.{PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.bellerophon.UnificationMatch
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.{GenProduct, PegasusProofHint}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools._
import org.apache.logging.log4j.scala.Logging

import scala.collection.immutable
import scala.collection.immutable.{IndexedSeq, List, Nil, Seq}

/**
 * Implementation: provides tactics for differential equations.
  *
  * @note Container for "complicated" tactics. Single-line implementations are in [[TactixLibrary]].
 * @see [[TactixLibrary.DW]], [[TactixLibrary.DC]]
 */
private object DifferentialTactics extends Logging {

  private val namespace = "differentialtactics"

  // QE with default timeout for use in ODE tactics (timeout in seconds)
  private[btactics] val ODE_QE_TIMEOUT = Integer.parseInt(Configuration(Configuration.Keys.ODE_TIMEOUT_FINALQE))
  private[btactics] def timeoutQE = QE(Nil, None, Some(ODE_QE_TIMEOUT))

  /** @see [[HilbertCalculus.DE]] */
  lazy val DE: DependentPositionTactic = new DependentPositionTactic("DE") {
    //@todo investigate why unification fails and causes unnecessarily complicated tactic. And get rid of duplicate implementation
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = if (RenUSubst.semanticRenaming) {
        if (isODESystem(sequent, pos)) {
          DESystemStep_SemRen(pos)*getODEDim(sequent, pos)
          //@todo unification fails
          // TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(provable.subgoals.head, pos)
        } else {
          useAt("DE differential effect")(pos)
        }
      } else {
        import ProofRuleTactics.contextualize
        if (isODESystem(sequent, pos)) {
          if (HilbertCalculus.INTERNAL) TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(sequent, pos)
          else contextualize(DESystemStep_NoSemRen, predictor)(pos)*getODEDim(sequent, pos)
          //@todo unification fails
          // TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(provable.subgoals.head, pos)
        } else {
          if (HilbertCalculus.INTERNAL) useAt("DE differential effect")(pos)
          else contextualize(DESystemStep_NoSemRen, predictor)(pos)
        }
      }

      private def predictor(fml: Formula): Formula = fml match {
        case Box(ODESystem(DifferentialProduct(AtomicODE(xp@DifferentialSymbol(x), t), c), h), p) =>
          Box(
            ODESystem(DifferentialProduct(c, AtomicODE(xp, t)), h),
            Box(Assign(xp, t), p)
          )

        case Box(ODESystem(AtomicODE(xp@DifferentialSymbol(x), t), h), p) =>
          Box(
            ODESystem(AtomicODE(xp, t), h),
            Box(Assign(xp, t), p)
          )
        case _ => logger.fatal("Unsure how to predict DE outcome for " + fml); ???
      }
    }

    /** A single step of DE system (@todo replace with useAt when unification for this example works) */
    // semanticRenaming
    private lazy val DESystemStep_SemRen: DependentPositionTactic = new DependentPositionTactic("DE system step") {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
          case Some(f@Box(ODESystem(DifferentialProduct(AtomicODE(d@DifferentialSymbol(x), t), c), h), p)) =>
            val g = Box(
              ODESystem(DifferentialProduct(c, AtomicODE(d, t)), h),
              Box(Assign(d, t), p)
            )

            //construct substitution
            val aF = UnitFunctional("f", AnyArg, Real)
            val aH = UnitPredicational("H", AnyArg)
            val aC = DifferentialProgramConst("c", AnyArg)
            val aP = UnitPredicational("p", AnyArg)
            val aX = Variable("x_")

            val subst = USubst(SubstitutionPair(aF, t) :: SubstitutionPair(aC, c) :: SubstitutionPair(aP, p) ::
              SubstitutionPair(aH, h) :: Nil)
            val uren = ProofRuleTactics.uniformRenaming(aX, x)
            val origin = Sequent(IndexedSeq(), IndexedSeq(s"[{${d.prettyString}=f(||),c&H(||)}]p(||) <-> [{c,${d.prettyString}=f(||)&H(||)}][${d.prettyString}:=f(||);]p(||)".asFormula))

            cutLR(g)(pos) <(
              /* use */ skip,
              //@todo conditional commuting (if (pos.isSucc) commuteEquivR(1) else Idioms.ident) instead?
              /* show */ cohide('Rlast) & equivifyR(1) & commuteEquivR(1) &
              TactixLibrary.US(subst, TactixLibrary.uniformRenameF(aX, x)(AxiomInfo("DE differential effect (system)").provable)))
              //TactixLibrary.US(subst, "DE differential effect (system)"))
        }
      }
    }

    /** A single step of DE system */
    // !semanticRenaming
    private lazy val DESystemStep_NoSemRen: DependentPositionTactic = new DependentPositionTactic("DE system step") {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
          case Some(f@Box(ODESystem(DifferentialProduct(AtomicODE(xp@DifferentialSymbol(x), t), c), h), p)) =>
            useAt("DE differential effect (system)")(pos)
          case Some(f@Box(ODESystem(AtomicODE(xp@DifferentialSymbol(x), t), h), p)) =>
            useAt("DE differential effect")(pos)
        }
      }
    }
  }

  /** @see [[TactixLibrary.dI]] */
  def diffInd(auto: Symbol = 'full): DependentPositionTactic = new DependentPositionTactic("dI") {
    require(auto == 'full || auto == 'none || auto == 'diffInd, "Expected one of ['none, 'diffInd, 'full] automation values, but got " + auto)
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        val diFml = sequent.sub(pos)

        require(pos.isSucc && (diFml match {
          case Some(Box(_: ODESystem, _)) => true
          case _ => false
        }), "diffInd only at ODE system in succedent, but got " + diFml)

        val expand = diFml match {
          case Some(Box(_, post)) if StaticSemantics.symbols(post).exists(
            { case Function(_, _, _, _, interpreted) => interpreted case _ => false }) =>
            // expand all interpreted function symbols below pos.1
            EqualityTactics.expandAllAt(pos ++ PosInExpr(1::Nil))
          case _ => skip
        }

        if (pos.isTopLevel) {
          val t = expand & DI(pos) &
            implyR(pos) & andR(pos) & Idioms.<(
              if (auto == 'full) ToolTactics.hideNonFOL & (QE & done | DebuggingTactics.done("Differential invariant must hold in the beginning"))
                 else skip,
              if (auto != 'none) {
                //@note derive before DE to keep positions easier
                derive(pos ++ PosInExpr(1 :: Nil)) &
                DE(pos) &
                (if (auto == 'full)
                  (Dassignb(pos ++ PosInExpr(1::Nil))*getODEDim(sequent, pos) | DebuggingTactics.error("After deriving, the right-hand sides of ODEs cannot be substituted into the postcondition")) &
                  //@note DW after DE to keep positions easier
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) & abstractionb(pos) & ToolTactics.hideNonFOL &
                    (QE & done | DebuggingTactics.done("Differential invariant must be preserved"))
                 else {
                  assert(auto == 'diffInd)
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                  abstractionb(pos) & SaturateTactic(allR(pos)) & ?(implyR(pos)) })
              } else skip
              )
          if (auto == 'full) Dconstify(t)(pos)
          else t
        } else {
          val t = expand & DI(pos) &
            (if (auto != 'none) {
              shift(PosInExpr(1 :: 1 :: Nil), "ANON" by ((pos: Position, sequent: Sequent) =>
                //@note derive before DE to keep positions easier
                shift(PosInExpr(1 :: Nil), derive)(pos) &
                  DE(pos) &
                  (if (auto == 'full) shift(PosInExpr(1 :: Nil), Dassignb)(pos)*getODEDim(sequent, pos) &
                    //@note DW after DE to keep positions easier
                    (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                    abstractionb(pos)
                  else abstractionb(pos))
                )
              )(pos)
            } else ident)
          if (auto == 'full) Dconstify(t)(pos)
          else t
        }
      }
    }
  }

  /**
   * diffInd: Differential Invariant proves a formula to be an invariant of a differential equation (by DI, DW, DE, QE)
    *
    * @example{{{
   *    x>=5 |- x>=5    x>=5 |- [{x'=2}](x>=5)'
   *    ---------------------------------------DIRule(qeTool)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5 |- [x:=x+1;](true->x>=5&[{x'=2}](x>=5)')
   *    ---------------------------------------------DIRule(qeTool)(1, 1::Nil)
   *    x>=5 |- [x:=x+1;][{x'=2}]x>=5
   * }}}
   * @incontext
   */
  lazy val DIRule: DependentPositionTactic = diffInd('none)
  lazy val diffIndRule: DependentPositionTactic = diffInd('diffInd)

  /** @see [[TactixLibrary.openDiffInd]] */
  val openDiffInd: DependentPositionTactic = new DependentPositionTactic("openDiffInd") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isSucc && pos.isTopLevel, "openDiffInd only at ODE system in succedent")
        val (axUse,der) = sequent.sub(pos) match {
          case Some(Box(_: ODESystem, _: Greater)) => ("DIo open differential invariance >",true)
          case Some(Box(_: ODESystem, _: Less)) => ("DIo open differential invariance <",true)

          case _ => throw new IllegalArgumentException("openDiffInd only at ODE system in succedent with an inequality in the postcondition (f>g,f<g), but got " + sequent.sub(pos))
        }
        if (pos.isTopLevel) {
          val t = useAt(axUse)(pos) <(
              testb(pos) & ToolTactics.hideNonFOL & QE & done,
              //@note derive before DE to keep positions easier
              implyR(pos) & (
                if(der) derive(pos ++ PosInExpr(1::1::Nil))
                else derive(pos ++ PosInExpr(1::1::0::Nil)) & derive(pos ++ PosInExpr(1::1::1::Nil))) &

                DE(pos) &
                (Dassignb(pos ++ PosInExpr(1::Nil))*getODEDim(sequent, pos) &
                  //@note DW after DE to keep positions easier
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) & abstractionb(pos) & ToolTactics.hideNonFOL & QE & done
                  )
              )
          Dconstify(t)(pos)
        } else {
          //@todo positional tactics need to be adapted
          val t = useAt(axUse)(pos) &
              shift(PosInExpr(1 :: 1 :: Nil), new DependentPositionTactic("Shift") {
                override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
                  override def computeExpr(sequent: Sequent): BelleExpr = {
                    //@note derive before DE to keep positions easier
                    //todo: needs fixing
                    (if(der) shift(PosInExpr(1 :: Nil), derive)(pos) else ident) &
                      DE(pos) &
                      shift(PosInExpr(1 :: Nil), Dassignb)(pos)*getODEDim(sequent, pos) &
                      //@note DW after DE to keep positions easier
                      (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                      abstractionb(pos)
                  }
                }
              }
              )(pos)
          Dconstify(t)(pos)
        }
      }
    }
  }

  /** @see [[TactixLibrary.diffVar]] */
  val diffVar: DependentPositionTactic = new DependentPositionTactic("diffVar") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        //require(pos.isSucc, "diffVar only at ODE system in succedent")
        val greater = sequent.sub(pos) match {
          case Some(Diamond(ODESystem(_,True), _: GreaterEqual)) => true
          case Some(Diamond(ODESystem(_,True), _: LessEqual)) => false
          case _ => throw new IllegalArgumentException("diffVar currently only implemented at ODE system with postcondition f>=g or f<=g and domain true, but got " + sequent.sub(pos))
        }
        val t = (if (greater)
          useAt("DV differential variant >=")
        else
          useAt("DV differential variant <="))(pos) & (
          // \exists e_ (e_>0 & [{c&true}](f(||)<=g(||) -> f(||)'>=g(||)'+e_))
          derive(pos ++ PosInExpr(0::1::1::1::0::Nil)) &
            derive(pos ++ PosInExpr(0::1::1::1::1::0::Nil)) &
            DE(pos ++ PosInExpr(0::1::Nil)) &
            (Dassignb(pos ++ PosInExpr(0::1::1::Nil))*getODEDim(sequent, pos) &
              abstractionb(pos ++ PosInExpr(0::1::Nil)) & QE & done
              )
          )
        t
      }
    }
  }

  /** @see [[TactixLibrary.dC()]] */
  def diffCut(formulas: Formula*): DependentPositionTactic =
    "dC" byWithInputs (formulas.toList, (pos, sequent) => {
      formulas.map(ghostDC(_, pos, sequent)(pos)).foldRight[BelleExpr](skip)((cut, all) => cut & Idioms.?(<(all, skip)))
    })

  /** Looks for special 'old' function symbol in f and creates DC (possibly with ghost) */
  private def ghostDC(f: Formula, origPos: Position, origSeq: Sequent): DependentPositionTactic = "ANON" by ((pos: Position, seq: Sequent) => {
    lazy val (ode, dc) = seq.sub(pos) match {
      case Some(Box(os: ODESystem, _)) => (os, DC _)
      case Some(Diamond(os: ODESystem, _)) => (os, DCd _)
    }

    val ov = FormulaTools.argsOf("old", f)
    if (ov.isEmpty) {
      if (FormulaTools.conjuncts(f).toSet.subsetOf(FormulaTools.conjuncts(ode.constraint).toSet)) skip else dc(f)(pos)
    } else {
      DLBySubst.discreteGhosts(ov, origSeq,
        (ghosts: List[((Term, Variable), BelleExpr)]) => {
          val posIncrements = if (pos.isTopLevel) 0 else ghosts.size
          val oldified = SubstitutionHelper.replaceFn("old", f, ghosts.map(_._1).toMap)
          if (FormulaTools.conjuncts(oldified).toSet.subsetOf(FormulaTools.conjuncts(ode.constraint).toSet)) skip
          else ghosts.map(_._2).reduce(_ & _) & dc(oldified)(pos ++ PosInExpr(List.fill(posIncrements)(1)))
        }
      )(pos)
    }
  })

  //Domain constraint refinement step for box/diamond ODEs on either (top-level) side of a sequent
  //Hides other succedents in the refinement subgoal by default, e.g.:
  // G|- [x'=f(x)&R]P, D     G|- [x'=f(x)&Q]R
  // --- dR
  // G|- [x'=f(x)&Q]P, D
  def diffRefine(f: Formula, hide: Boolean=true): DependentPositionTactic =
    "dR" byWithInputs (f::/* todo unsupported argument type (argument not used from UI yet) hide::*/Nil,(pos,sequent) => {
    require(pos.isTopLevel, "dR only at top-level succedents/antecedents")
    val (newFml,ax) = sequent.sub(pos) match {
      case Some(Diamond(sys: ODESystem, post)) => (Diamond(ODESystem(sys.ode,f),post),DerivedAxioms.DiffRefineDiamond.fact)
      case Some(Box(sys: ODESystem, post)) => (Box(ODESystem(sys.ode,f),post),DerivedAxioms.DiffRefine.fact)
      case _ => throw new IllegalArgumentException("dR only for box/diamond ODEs")
    }
    val cpos = if (pos.isSucc) Fixed(pos) else LastSucc(0)

    cutLR(newFml)(pos) <(skip,useAt(ax,PosInExpr(1::Nil))(cpos) & (if(hide) cohideOnlyR(cpos) else skip))
  })

  /** @see [[TactixLibrary.diffInvariant]] */
  def diffInvariant(formulas: Formula*): DependentPositionTactic =
    "diffInvariant" byWithInputs (formulas.toList, (pos, sequent) => {
      //@note assumes that first subgoal is desired result, see diffCut
      //@note UnifyUSCalculus leaves prereq open at last succedent position
      val diffIndAllButFirst = skip +: Seq.tabulate(formulas.length)(_ => diffInd()(SuccPosition.base0(sequent.succ.size-1, pos.inExpr)) & QE & done)
      diffCut(formulas: _*)(pos) <(diffIndAllButFirst:_*)
    })

  /** Inverse differential cut, removes the last conjunct from the evolution domain constraint. */
  def inverseDiffCut: DependentPositionTactic = "dCi" by ((pos: Position, s: Sequent) => {
    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)
    val fact = s.at(pos) match {
      case (ctx, fml: Modal) =>
        val (remainder, last) = fml.program match {
          case ODESystem(_, And(l, r)) => (l, r)
          case ODESystem(_, edc) => (True, edc)
        }
        val factFml =
          if (polarity > 0) Imply(last, Imply(fml.replaceAt(PosInExpr(0::1::Nil), remainder), fml))
          else Imply(last, Imply(fml, ctx(fml.replaceAt(PosInExpr(0::1::Nil), remainder))))
        proveBy(factFml,
          implyR(1)*2 & diffCut(last)(if (polarity > 0) -2 else 1) <(
            Idioms.?(useAt("true&")(-2, PosInExpr(0::1::Nil))) & close
            ,
            cohideOnlyR('Rlast) & diffInd()(1) & DebuggingTactics.done
          )
        )
    }

    useAt(fact, PosInExpr(1::(if (polarity > 0) 1 else 0)::Nil))(pos)
  })

  /**
    * Turns things that are constant in ODEs into function symbols.
    *
    * @example Turns v>0, a>0 |- [v'=a;]v>0, a>0 into v>0, a()>0 |- [v'=a();]v>0, a()>0
    * @return The tactic.
    */
  def Dconstify(inner: BelleExpr): DependentPositionTactic = TacticFactory.anon ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(ode@ODESystem(_, _), p)) =>
        val consts = (StaticSemantics.freeVars(p) -- StaticSemantics.boundVars(ode)).toSet.filter(_.isInstanceOf[BaseVariable])
        consts.foldLeft[BelleExpr](inner)((tactic, c) =>
          let(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c, tactic))
      case Some(Diamond(ode@ODESystem(_, _), p)) =>
        val consts = (StaticSemantics.freeVars(p) -- StaticSemantics.boundVars(ode)).toSet.filter(_.isInstanceOf[BaseVariable])
        consts.foldLeft[BelleExpr](inner)((tactic, c) =>
          let(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c, tactic))
    }
  })

 /** Add constant context into the domain constraint at a given (top-level) position by V
   * @example Turns v>0, a>0 |- [v'=a]v>0 into v>0, a>0 |- [v'=a & a>0]v>0
   */
 def DconstV : DependentPositionTactic = "DconstV" by ((pos:Position,seq:Sequent) => {
    require(pos.isTopLevel, "DconstV only at top-level positions")
    val dom = seq.sub(pos) match {
      case Some(Box(ODESystem(_, dom), p)) => dom
      case Some(Diamond(ODESystem(_, dom), p)) => dom
      case _ => throw new BelleThrowable("DconstV adds constants into domain constraint for box/diamond ODEs")
    }

    //The constant context
    val constCtxt = TacticHelper.propertiesOfConstants(seq,pos.checkTop)
    if(constCtxt.isEmpty)
      skip
    else {
      val newDom = constCtxt.foldRight(dom)((x, y) => And(x, y))
      dR(newDom)(pos) <( skip,
         //propositional proof should be sufficient here
        (boxAnd(1) & andR(1)<(V(1) & closeId,skip))*constCtxt.length &
         diffWeakenG(1) & implyR(1) & closeId)
    }
  })

  /** Simplify a top-level succedent box ODE with the domain constraint
    * This uses the default simplifier configuration
    * @example Turns |- [v'=a & a>0](a>0&v>0) into |- [v'=a & a>0]v>0
    */
  def domSimplify : DependentPositionTactic = "domSimplify" by ((pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "domSimplify currently only works at top-level succedents")

    val (ode,post) = seq.sub(pos) match {
      case Some(Box(ode @ ODESystem(_,_), post)) => (ode,post)
      case _ => throw new BelleThrowable("domSimplify only applies to box ODEs")
    }

    //todo: How to exactly simulate behavior of andL('L)*?? flattenConjunctions doesn't match it
    val ctx = proveBy(Sequent(IndexedSeq(ode.constraint),IndexedSeq(False)), SaturateTactic(andL('L))).subgoals(0).ante

    val (f,propt) = SimplifierV3.simpWithDischarge(ctx,post,SimplifierV3.defaultFaxs,SimplifierV3.defaultTaxs)
    //val (f,propt) = SimplifierV3.simpWithDischarge(flattenConjunctions(ode.constraint).toIndexedSeq,post,SimplifierV3.defaultFaxs,SimplifierV3.defaultTaxs)
    propt match {
      case None => skip
      case Some(pr) =>
        cutR (Box (ode, f) ) (pos) < (skip,
        cohideR (pos) & implyR(1) & DW(1) & monb & implyR(1) & implyRi & SaturateTactic(andL('L)) & equivifyR(1) &
        commuteEquivR(1) & by(pr)
        )
    }
  })

  /** DG: Differential Ghost add auxiliary differential equations with extra variables `y'=a*y+b`.
    * `[x'=f(x)&q(x)]p(x)` reduces to `\exists y [x'=f(x),y'=a*y+b&q(x)]p(x)`.
    *
    * @example{{{
    *         |- \exists y [{x'=2,y'=0*y+1}]x>0
    *         ---------------------------------- DG("{y'=0*y+1}".asDifferentialProgram)(1)
    *         |- [{x'=2}]x>0
    * }}}
    * @example{{{
    *         |- \exists y [{x'=2,y'=f()*y+g() & x>=0}]x>0
    *         --------------------------------------------- DG("{y'=f()*y+g()}".asDifferentialProgram)(1)
    *         |- [{x'=2 & x>=0}]x>0
    * }}}
    * @param ghost A differential program of the form y'=a*y+b or y'=a*y or y'=b.
    * @see [[dG()]]
    */
  private def DG(ghost: DifferentialProgram): DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => {
    val (y, a, b) = DifferentialHelper.parseGhost(ghost)

    sequent.sub(pos) match {
      case Some(Box(ode@ODESystem(c, h), p)) if !StaticSemantics(ode).bv.contains(y) &&
        !StaticSemantics.symbols(a).contains(y) && !StaticSemantics.symbols(b).contains(y) =>

        //SOUNDNESS-CRITICAL: DO NOT ALLOW SINGULARITIES IN GHOSTS.
        //@TODO This is a bit hacky. We should either:
        //  1) try to cut <(nil, dI(1)) NotEqual(v, Number(0)) before doing
        //     the ghost, and only check for that here; or
        //  2) insist on NotEqual and provide the user with an errormessage.
        //But ultimately, we need a systematic way of checking this in the
        //core (last-case resort could always just move this check into the core and apply
        //it whenever DG differential ghost is applied, but that's pretty
        //hacky).
        val singular = {
          val evDomFmls = flattenConjunctions(h)
          (FormulaTools.singularities(a) ++ FormulaTools.singularities(b)).filter(v =>
            !evDomFmls.contains(Less(v, Number(0)))     &&
            !evDomFmls.contains(Less(Number(0), v))     &&
            !evDomFmls.contains(Greater(v, Number(0)))  &&
            !evDomFmls.contains(Greater(Number(0), v))  &&
            !evDomFmls.contains(NotEqual(v, Number(0))) &&
            !evDomFmls.contains(Greater(Number(0), v))
          )
        }

        if (!singular.isEmpty)
          throw new BelleThrowable("Possible singularities during DG(" + ghost + ") will be rejected: " +
            singular.mkString(",") + " in\n" + sequent.prettyString +
            "\nWhen dividing by a variable v, try cutting v!=0 into the evolution domain constraint"
          )

        (a, b) match {
          case (Number(n), _) if n == 0 =>
            val subst = (us: Option[Subst]) => us.getOrElse(throw BelleUnsupportedFailure("DG expects substitution result from unification")) ++ RenUSubst(
              (Variable("y_",None,Real), y) ::
                (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), b) :: Nil)
            useAt("DG differential ghost constant", PosInExpr(0::Nil), subst)(pos)
          case (_, Neg(Number(n))) =>
            val subst = (us: Option[Subst]) => us.getOrElse(throw BelleUnsupportedFailure("DG expects substitution result from unification")) ++ RenUSubst(
              (Variable("y_",None,Real), y) ::
                (UnitFunctional("a", Except(Variable("y_", None, Real)), Real), a) ::
                (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), Number(-n)) :: Nil)
            useAt("DG differential ghost", PosInExpr(0::Nil), subst)(pos)
          case _ =>
            val subst = (us: Option[Subst]) => us.getOrElse(throw BelleUnsupportedFailure("DG expects substitution result from unification")) ++ RenUSubst(
              (Variable("y_",None,Real), y) ::
                (UnitFunctional("a", Except(Variable("y_", None, Real)), Real), a) ::
                (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), b) :: Nil)
            useAt("DG differential ghost", PosInExpr(0::Nil), subst)(pos)
        }
    }
  })

  /** @see [[TactixLibrary.dG]] */
  def dG(ghost: DifferentialProgram, r: Option[Formula]): DependentPositionTactic = "dG" byWithInputs (
      r match { case Some(rr) => ghost :: rr :: Nil case None => ghost :: Nil },
      (pos: Position, sequent: Sequent) => r match {
        case Some(rr) if r != sequent.sub(pos ++ PosInExpr(1::Nil)) => DG(ghost)(pos) & transform(rr)(pos ++ PosInExpr(0::1::Nil))
        case _ => DG(ghost)(pos) //@note no r or r==p
      })

  /**
    * Removes the left-most DE from a system of ODEs:
    * {{{
    *   [v'=a,t'=1 & q]p
    *   ---------------------- dGi
    *   [x'=v,v'=a,t'=1 & q]p
    * }}}
    */
  def inverseDiffGhost: DependentPositionTactic = "dGi" by ((pos: Position, s: Sequent) => {
    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)
    s.sub(pos) match {
      case Some(f@Box(ODESystem(DifferentialProduct(y_DE: AtomicODE, _), _), _)) if polarity > 0 =>
        val axiomName = "DG inverse differential ghost implicational"
        //Cut in the right-hand side of the equivalence in the [[axiomName]] axiom, prove it, and then performing rewriting.
        TactixLibrary.cutAt(Forall(y_DE.xp.x::Nil, f))(pos) <(
          HilbertCalculus.useExpansionAt(axiomName)(pos)
          ,
          (if (pos.isSucc) TactixLibrary.cohideR(pos.top) else TactixLibrary.cohideR('Rlast)) &
            HilbertCalculus.useAt("all eliminate")(1, PosInExpr((if (pos.isSucc) 0 else 1) +: pos.inExpr.pos)) &
            TactixLibrary.useAt(DerivedAxioms.implySelf)(1) & TactixLibrary.closeT & DebuggingTactics.done
        )
      case Some(Box(ODESystem(DifferentialProduct(y_DE: AtomicODE, c), q), p)) if polarity < 0 =>
        //@note must substitute manually since DifferentialProduct reassociates (see cutAt) and therefore unification won't match
        val subst = (_: Option[TactixLibrary.Subst]) =>
          RenUSubst(
            ("y_".asTerm, y_DE.xp.x) ::
              ("b(|y_|)".asTerm, y_DE.e) ::
              ("q(|y_|)".asFormula, q) ::
              (DifferentialProgramConst("c", Except("y_".asVariable)), c) ::
              ("p(|y_|)".asFormula, p.replaceAll(y_DE.xp.x, "y_".asVariable)) ::
              Nil)

        //Cut in the right-hand side of the equivalence in the [[axiomName]] axiom, prove it, and then rewrite.
        HilbertCalculus.useAt(", commute", PosInExpr(1::Nil))(pos) &
          TactixLibrary.cutAt(Exists(y_DE.xp.x::Nil, Box(ODESystem(DifferentialProduct(c, y_DE), q), p)))(pos) <(
            HilbertCalculus.useAt("DG differential ghost constant", PosInExpr(1::Nil), subst)(pos)
            ,
            (if (pos.isSucc) TactixLibrary.cohideR(pos.top) else TactixLibrary.cohideR('Rlast)) &
              TactixLibrary.CMon(pos.inExpr) & TactixLibrary.implyR(1) &
              TactixLibrary.existsR(y_DE.xp.x)(1) & TactixLibrary.closeId
          )
    }
  })

  /** @see [[HilbertCalculus.Derive.Dvar]] */
  //@todo could probably simplify implementation by picking atomic formula, using "x' derive var" and then embedding this equivalence into context by CE.
  //@todo Or, rather, by using CE directly on a "x' derive var" provable fact (z)'=1 <-> z'=1.
  lazy val Dvariable: DependentPositionTactic = new DependentPositionTactic("Dvariable") {
    private val OPTIMIZED = true //@todo true
    private val axiom = AxiomInfo("x' derive var commuted")
    private val (keyCtx:Context[_],keyPart) = axiom.formula.at(PosInExpr(1::Nil))
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {

      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(Differential(x: Variable)) =>
          if (OPTIMIZED) {
            logger.debug("Dvariable " + keyPart + " on " + x)
            val fact = UnificationMatch.apply(keyPart, Differential(x)).toForward(axiom.provable)
            CEat(fact)(pos)
          } else {
            val withxprime: Formula = sequent.replaceAt(pos, DifferentialSymbol(x)).asInstanceOf[Formula]
            val axiom = s"\\forall ${x.prettyString} (${x.prettyString})' = ${x.prettyString}'".asFormula
            cutLR(withxprime)(pos.topLevel) <(
              /* use */ skip,
              /* show */ cohide(pos.top) & CMon(formulaPos(sequent(pos.top), pos.inExpr)) & cut(axiom) <(
              useAt("all eliminate")(-1) & eqL2R(-1)(1) & useAt("-> self")(1) & close,
              cohide('Rlast) & byUS(DerivedAxioms.Dvariable))
              )
          }
        }
      }

    /** Finds the first parent of p in f that is a formula. Returns p if f at p is a formula. */
    private def formulaPos(f: Formula, p: PosInExpr): PosInExpr = {
      f.sub(p) match {
        case Some(_: Formula) => p
        case _ => formulaPos(f, p.parent)
      }
    }
  }

  /**
   * Unpacks the evolution domain of an ODE at time zero. Useful for proofs that rely on contradictions with other
   * conditions at time zero preventing continuous evolution in the ODE.
   * {{{
   *  x<0, x>=0 |- [x'=3,y'=2 & x>=0]y>0
   *  -----------------------------------diffUnpackEvolutionDomainInitially(1)
   *        x<0 |- [x'=3,y'=2 & x>=0]y>0
   * }}}
   */
  lazy val diffUnpackEvolutionDomainInitially: DependentPositionTactic = "diffUnpackEvolDomain" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(ODESystem(_, q), _)) =>
      require(pos.isSucc && pos.isTopLevel, "diffUnpackEvolDomain only at top-level in succedent")
      cut(q) <(
        /* use */ skip,
        /* show */ DI(pos) & implyR(pos) & closeIdWith('Llast)
        )
  })

  /** diffWeaken by diffCut(consts) <(diffWeakenG, V&close) */
  lazy val diffWeaken: DependentPositionTactic = "dW" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(a: ODESystem, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeaken only at top level in succedent")

      if (sequent.succ.size <= 1) {
        val primedVars = DifferentialHelper.getPrimedVariables(a)

        val rewriteExistingGhosts = sequent.ante.zipWithIndex.filter({
          case (Equal(l: Variable, r: Variable), _) => primedVars.contains(r) && !primedVars.contains(l)
          case _ => false
        }).reverse.map({ case (_, i) => exhaustiveEqR2L(AntePosition.base0(i)) & hideL(AntePosition.base0(i)) }).
          reduceOption[BelleExpr](_&_).getOrElse(skip)


        val storeInitialVals = "ANON" by ((seq: Sequent) => {
          val anteSymbols = seq.ante.flatMap(StaticSemantics.symbols)
          val storePrimedVars = primedVars.filter(anteSymbols.contains)
          storePrimedVars.
            map(discreteGhost(_)(pos)).reduceOption[BelleExpr](_&_).getOrElse(skip) &
            (DLBySubst.assignEquality(pos) & exhaustiveEqR2L('Llast) & hideL('Llast))*storePrimedVars.size
        })

        val dw = "ANON" by ((seq: Sequent) => {
          diffWeakenG(pos) & implyR(1) & andL('Llast)*seq.ante.size & implyRi
        })

        val cutAllAntes = "ANON" by ((seq: Sequent) => {
          if (seq.ante.isEmpty) skip
          //@note all ante formulas rewritten to initial values at this point
          else diffCut(seq.ante.reduceRight(And))(pos) <(
            skip,
            V('Rlast) & (andR('Rlast) <(closeIdWith('Rlast) & done, skip))*(seq.ante.size-1) & closeIdWith('Rlast) & done
          )
        })

        rewriteExistingGhosts & storeInitialVals & cutAllAntes & dw
      } else {
        useAt("DW differential weakening")(pos) & abstractionb(pos) & SaturateTactic(allR('Rlast))
      }
  })

  /** diffWeaken by DW & G */
  lazy val diffWeakenG: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(_: ODESystem, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeakenG only at top level in succedent")
      cohide(pos.top) & DW(1) & G(1)
  })

  //A user-friendly error message displayed when ODE can't find anything useful to do.
  private val failureMessage = "ODE automation was neither able to prove the postcondition invariant nor automatically find new ODE invariants."+
    " Try annotating the ODE with additional invariants or refining the evolution domain with a differential cut."

  /** Assert LZZ succeeds at a certain position. */
  lazy val lzzCheck: BuiltInPositionTactic = {
    def constConditions(formulas: IndexedSeq[Formula], taboo: SetLattice[Variable]): IndexedSeq[Formula] = {
      formulas.filter(StaticSemantics.freeVars(_).intersect(taboo).isEmpty)
    }

    DebuggingTactics.assert((invSeq: Sequent, invPos: Position) => {
      invSeq.sub(invPos) match {
        case Some(Box(ode: ODESystem, invCandidate)) => ToolProvider.invGenTool() match {
          case Some(invTool) =>
            //@todo constant conditions at the sub position
            val topFml = invSeq.sub(invPos.top).get.asInstanceOf[Formula]
            val consts = constConditions(
              invSeq.ante.flatMap(FormulaTools.conjuncts),
              StaticSemantics(topFml).bv).reduceRightOption(And)
            val strengthenedCandidate = consts match {
              case Some(c) => And(c, invCandidate)
              case None => invCandidate
            }
            try {
              invTool.lzzCheck(ode, strengthenedCandidate)
            } catch {
              // cannot falsify for whatever reason (timeout, ...), so continue with the tactic
              case _: Exception => true
            }
          case _ => true
        }
        case _ => false
      }
    }, "Invariant fast-check failed")
  }


  /** Counterexample finder
    * Fails with an error message if it finds a counterexample but succeeds in all other cases
    * (including when the sequent or position are not of the expected shape)
    */
  lazy val cexCheck: DependentPositionTactic = "cexCheck" by ((pos: Position, seq:Sequent) => {
    if (!(pos.isSucc && pos.isTopLevel && pos.checkSucc.index0 == 0 && seq.succ.length==1)) {
      //todo: currently only works if there is exactly one succedent
      logger.warn("ODE counterexample not called at top-level succedent")
      skip
    } else if (ToolProvider.invGenTool().isEmpty) {
      logger.warn("ODE counterexample requires an InvGenTool, but got None")
      skip
    } else {
      val tool = ToolProvider.invGenTool().get

      seq.sub(pos) match {
        case Some(Box(ode:ODESystem, post)) =>
          try {
            tool.refuteODE(ode, seq.ante, post) match {
              case None => skip
              case Some(_) => cut(False) <(closeF, cohideR('Rlast))
            }
          } catch {
            // cannot falsify for whatever reason (timeout, ...), so continue with the tactic
            case _: Exception => skip
          }
        case _ =>
          logger.warn("ODE counterexample not called at box ODE in succedent")
          skip
      }
    }
  })

  /** Tries to instantiate the evolution domain fact with the ODE duration (assumes monotonicity). */
  lazy val endODEHeuristic: BelleExpr = "ANON" by ((seq: Sequent) => {
    val instantiators = (seq.ante.indices.map(AntePosition.base0(_)) ++ seq.succ.indices.map(SuccPosition.base0(_))).
      flatMap(pos => {
        Idioms.mapSubpositions(pos, seq, {
          case (Forall((s@BaseVariable("s_", _, Real))::Nil, Imply(And(
          LessEqual(_, BaseVariable("s_", _, Real)),
          LessEqual(BaseVariable("s_", _, Real), t@BaseVariable("t_", _, Real))), _)), pp: Position) =>
            Some(allL(s, t)(pp))
          case _ => None
        })
    })

    instantiators.reduceOption[BelleExpr](_ & _).getOrElse(skip) & QE & done
  })

  /**
    * @see [[TactixLibrary.ODE]]
    * @author Andre Platzer
    * @author Nathan Fulton
    * @author Stefan Mitsch
    * @note Compatibility tactic for Z3 ([[DifferentialTactics.odeInvariant]] not supported with Z3).
    */
  lazy val ODE: DependentPositionTactic = "ODE" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(sys@ODESystem(ode, q), _)) =>
      lazy val recurseODE = ODE(useOdeInvariant = false, introduceStuttering = true,
        //@note abort if unchanged
        assertT((sseq: Sequent, ppos: Position) => !sseq.sub(ppos ++ PosInExpr(0::Nil)).contains(sys),
          failureMessage
        )(pos) &
          ("ANON" by ((ppos: Position, sseq: Sequent) => sseq.sub(ppos) match {
            case Some(ODESystem(_, extendedQ)) =>
              if (q == True && extendedQ != True) useAt("true&")(ppos ++
                PosInExpr(1 +: FormulaTools.posOf(extendedQ, q).getOrElse(PosInExpr.HereP).pos.dropRight(1)))
              else skip
          })) (pos ++ PosInExpr(0 :: Nil))
      )(pos)

      if (pos.isTopLevel) {
        proveWithoutCuts(false)(pos) |
        solve(pos) & ?(endODEHeuristic) |
        recurseODE
      } else {
        //@note diffInd in context won't fail even if unprovable in the end; try solve first to support the usual examples
        solve(pos) & ?(endODEHeuristic) |
        proveWithoutCuts(false)(pos) |
        recurseODE
      }
  })

  /** Compatibility ODE invariance tactics prior to [[DifferentialTactics.odeInvariant]] */
  private def compatibilityFallback(pos: Position, isOpen: Boolean): BelleExpr =
    lzzCheck(pos) &
      (if (isOpen) {
        openDiffInd(pos) | DGauto(pos) //> TODO: needs updating
      } else {
        diffInd()(pos)       | // >= to >=
          DGauto(pos)          |
          dgZeroMonomial(pos)  | //Equalities
          dgZeroPolynomial(pos)  //Equalities
      })

  /** Proves ODE invariance properties. */
  private val proveInvariant = "ANON" by ((pos: Position, seq: Sequent) => {
    val post: Formula = seq.sub(pos) match {
      case Some(Box(ode: ODESystem, pf)) => pf
      case Some(ow) => throw new BelleThrowable("ill-positioned " + pos + " does not give a differential equation in " + seq)
      case None => throw new BelleThrowable("ill-positioned " + pos + " undefined in " + seq)
    }
    val isOpen = post match {
      case  _: Greater => true
      case _: Less => true
      case _ => false
    }
    TactixLibrary.odeInvariant(pos) | compatibilityFallback(pos, isOpen)
  })

  /** Tries to prove ODE properties without invariant generation or solving. */
  private def proveWithoutCuts(useOdeInvariant: Boolean) = "ANON" by ((pos: Position) => {
    SaturateTactic(boxAnd(pos) & andR(pos)) &
      onAll(("ANON" by ((pos: Position, seq: Sequent) => {
        val (ode:ODESystem, post:Formula) = seq.sub(pos) match {
          case Some(Box(ode: ODESystem, pf)) => (ode, pf)
          case Some(ow) => throw new BelleThrowable("ill-positioned " + pos + " does not give a differential equation in " + seq)
          case None => throw new BelleThrowable("ill-positioned " + pos + " undefined in " + seq)
        }

        val bounds = StaticSemantics.boundVars(ode.ode).symbols //@note ordering irrelevant, only intersecting/subsetof
        val frees = StaticSemantics.freeVars(post).symbols      //@note ordering irrelevant, only intersecting/subsetof

        val isOpen = post match {
          case  _: Greater => true
          case _: Less => true
          case _ => false
        }

        //@note diffWeaken will already include all cases where V works, without much additional effort.
        (if (frees.intersect(bounds).subsetOf(StaticSemantics.freeVars(ode.constraint).symbols))
          diffWeaken(pos) & QE(Nil, None, Some(Integer.parseInt(Configuration(Configuration.Keys.ODE_TIMEOUT_FINALQE)))) & done else fail
          ) | (if (useOdeInvariant) proveInvariant(pos)
        else compatibilityFallback(pos, isOpen))
      })) (pos))
  })

  private def ODE(useOdeInvariant: Boolean, introduceStuttering: Boolean, finish: BelleExpr): DependentPositionTactic = "ODE" by ((pos: Position, seq: Sequent) => {
    val invariantCandidates = try {
      InvariantGenerator.differentialInvariantGenerator(seq,pos)
    } catch {
      case err: Exception =>
        logger.warn("Failed to produce a proof for this ODE. Underlying cause: ChooseSome: error listing options " + err)
        Stream[GenProduct]()
    }

    //Adds an invariant to the system's evolution domain constraint and tries to establish the invariant via proveWithoutCuts.
    //Fails if the invariant cannot be established by proveWithoutCuts.
    val addInvariant = ChooseSome(
      () => invariantCandidates.iterator,
      (prod: GenProduct) => prod match {
        case (inv, _) =>
          DebuggingTactics.debug(s"[ODE] Trying to cut in invariant candidate: $inv") &
          /*@note diffCut skips previously cut in invs, which means <(...) will fail and we try the next candidate */
          diffCut(inv)(pos) <(skip, proveInvariant(pos) & done)
      }
    )

    //If lateSolve is true then diffSolve will be run last, if at all.
    val insistOnProof = pos.isTopLevel //@todo come up wtih better heuristic for determining when to insist on a proof being completed. Solvability is a pretty decent heuristic.

    /** Introduces stuttering assignments for each BV of the ODE */
    val stutter = "ANON" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(a: ODESystem, _)) =>
        val primedVars = StaticSemantics.boundVars(a).toSet[Variable].filter(_.isInstanceOf[BaseVariable])
        primedVars.map(DLBySubst.stutter(_)(pos ++ PosInExpr(1::Nil))).reduceOption[BelleExpr](_&_).getOrElse(skip)
    })

    val unstutter = "ANON" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(a: ODESystem, _)) =>
        val primedVars = StaticSemantics.boundVars(a).toSet[Variable].filter(_.isInstanceOf[BaseVariable])
        (1 to primedVars.size).reverse.map(i => ?(assignb(pos ++ PosInExpr(List.fill(i)(1))))).
          reduceOption[BelleExpr](_&_).getOrElse(skip)
      case _ => skip
    })

    if (insistOnProof)
      proveWithoutCuts(useOdeInvariant)(pos)        |
      (addInvariant & ODE(useOdeInvariant=true, introduceStuttering,finish)(pos))    |
      splitWeakInequality(pos)<(ODE(useOdeInvariant=true, introduceStuttering,finish)(pos), ODE(useOdeInvariant=true, introduceStuttering,finish)(pos)) |
      (if (introduceStuttering) stutter(pos) & ODE(useOdeInvariant=true, introduceStuttering=false,finish)(pos) & unstutter(pos)
       else finish)
    else
      (proveWithoutCuts(useOdeInvariant)(pos) & done)   |
      (addInvariant & ODE(useOdeInvariant=true, introduceStuttering,finish)(pos) & done) |
      (splitWeakInequality(pos) <(
        ODE(useOdeInvariant=true, introduceStuttering,finish)(pos),
        ODE(useOdeInvariant=true, introduceStuttering,finish)(pos)) & done) |
      (if (introduceStuttering) stutter(pos) & ODE(useOdeInvariant=true, introduceStuttering=false, finish)(pos) & unstutter(pos) & done
       else finish)
  })

  /** Fast ODE implementation. Tries the provided `invariantCandidates`. Tactic `finish` is executed when fastODE itself cannot find a proof. */
  private def fastODE(invariantCandidates: Iterator[GenProduct])(finish: BelleExpr): DependentPositionTactic = "ODE" by ((pos: Position, seq: Sequent) => {
    //Adds invariants to the system's evolution domain constraint and tries to establish them via odeInvariant.
    //Fails if the invariants cannot be established by odeInvariant.
    val addInvariant = ChooseSome(
      () => invariantCandidates,
      (prod: GenProduct) => prod match {
        case (inv, proofHint) =>
          DebuggingTactics.debug(s"[ODE] Trying to cut in invariant candidate: $inv") &
            /*@note diffCut skips previously cut in invs, which means <(...) will fail and we try the next candidate */
            diffCut(inv)(pos) <(
              skip,
              proofHint match {
                case Some(PegasusProofHint(_, None)) => odeInvariant(tryHard = true, useDw = false)(pos)
                case _ => odeInvariant(tryHard = false, useDw = false)(pos)
              }
            ) &
          // continue outside <(skip, ...) so that cut is proved before used
          (odeInvariant()(pos) | fastODE(invariantCandidates)(finish)(pos) /* with next option from iterator */) &
          DebuggingTactics.debug("[ODE] Inv Candidate done")
      }
    )

    addInvariant | finish
  })

  /**
    * @see [[TactixLibrary.ODE]]
    * @author Andre Platzer
    * @author Nathan Fulton
    * @author Stefan Mitsch
    */
  lazy val mathematicaODE: DependentPositionTactic = "ODE" by ((pos: Position, seq: Sequent) => {
    require(pos.isSucc && pos.isTopLevel, "ODE automation only applicable to top-level succedents")

    seq.sub(pos) match {
      case Some(Box(sys@ODESystem(ode, q), _)) =>
        // Try to prove postcondition invariant
        odeInvariant()(pos) |
        // Counterexample check
        cexCheck(pos) & doIf(!_.subgoals.exists(_.succ.forall(_ == False)))(
          // Some additional cases
          //(solve(pos) & ?(timeoutQE))|
          ODEInvariance.nilpotentSolve(true)(pos) |
          // todo: Pegasus should tell us for nonlinear ODEs
          // (diffUnpackEvolutionDomainInitially(pos) & DebuggingTactics.print("diff unpack") & hideR(pos) & timeoutQE & done) |
          // todo: Insert G|-[x'=f(x)]P refutation here
          // Ask for invariants and recursively tries to diff cut them in
          // aborts with error if no extra cuts were found
          fastODE(
            try {
              InvariantGenerator.differentialInvariantGenerator(seq,pos).iterator
            } catch {
              case err: Exception =>
                logger.warn("Failed to produce a proof for this ODE. Underlying cause: ChooseSome: error listing options " + err)
                Stream[GenProduct]().iterator
            }
          )(
            //@note aborts with error if the ODE was left unchanged -- invariant generators failed
            assertT((sseq: Sequent, ppos: Position) => !sseq.sub(ppos ++ PosInExpr(0::Nil)).contains(sys),
              failureMessage
            )(pos) &
              ("ANON" by ((ppos: Position, sseq: Sequent) => sseq.sub(ppos) match {
                case Some(ODESystem(_, extendedQ)) =>
                  if (q == True && extendedQ != True) useAt("true&")(ppos ++
                    PosInExpr(1 +: FormulaTools.posOf(extendedQ, q).getOrElse(PosInExpr.HereP).pos.dropRight(1)))
                  else skip
              })) (pos ++ PosInExpr(0 :: Nil))
          )(pos)
        )
      case _ => throw new BelleThrowable("ODE automation only applies to box ODEs.")
    }
  })

  /** Splits a post-condition containing a weak inequality into an open set case and an equillibrium point case.
    * Given a formula of the form [ode]p<=q, produces two new subgoals of the forms [ode]p < q and  [ode]p=q.
    * @see http://nfulton.org/2017/01/14/Ghosts/#ghosts-for-closedclopen-sets
    * @author Nathan Fulton */
  def splitWeakInequality : DependentPositionTactic = "splitWeakInequality" by ((pos: Position, seq: Sequent) => {
    val postcondition = seq.at(pos)._2 match {
      case Box(ODESystem(_,_), p) => p
      case _ => throw new BelleThrowable("splitWeakInequality is only applicable for ODE's with weak inequalities as post-conditions.")
    }
    val (lhs, rhs, openSetConstructor) = postcondition match {
      case GreaterEqual(l,r) => (l,r,Greater)
      case LessEqual(l,r)    => (l,r,Less)
      case _                 => throw new BelleThrowable(s"splitWeakInequality Expected a weak inequality in the post condition (<= or >=) but found: ${postcondition}")
    }

    val caseDistinction = Or(openSetConstructor(lhs,rhs), Equal(lhs,rhs))

    cut(caseDistinction) <(
      orL('Llast) <(
        generalize(openSetConstructor(lhs,rhs))(1) <(skip, QE & done),
        generalize(Equal(lhs,rhs))(1) <(skip, QE & done)
      )
      ,
      (hide(pos.topLevel) & QE & done) | //@todo write a hideNonArithmetic tactic.
      DebuggingTactics.assert(_=>false, s"splitWeakInequality failed because $caseDistinction does not hold initially.")
    )
  })

  def dgZeroPolynomial : DependentPositionTactic = "dgZeroPolynomial" by ((pos: Position, seq:Sequent) => {
    val Some(Box(ODESystem(system, constraint), property)) = seq.sub(pos)

    val lhs = property match {
      case Equal(term, Number(n)) if n == 0 => term
      case _ => throw new BelleThrowable(s"Not sure what to do with shape ${seq.sub(pos)}")
    }

    val (x: Variable, derivative:Term) = system match {
      case AtomicODE(xp, t) => (xp.x, t)
      case _ => throw new BelleThrowable("Systems not currently supported by dgZeroPolynomialDerivative")
    }
    require(lhs == x, "Currently require that the post-condition is of the form x=0 where x is the primed variable in the ODE.")

    val ghostVar = "z_".asVariable
    require(!StaticSemantics.vars(system).contains(ghostVar), "fresh ghost " + ghostVar + " in " + system.prettyString) //@todo should not occur anywhere else in the sequent either...

    val negOneHalf: Term = Divide(Number(-1), Number(2))
    //Given a system of the form x'=f(x), this returns (f(x))'/x simplified so that x does not occur on the denom.
    //@note this is done because we can't ghost in something that contains a division by a possibly zero-valued variable (in this case, x).
    val xPrimeDividedByX = TacticHelper.transformMonomials(derivative, (t:Term) => t match {
      case Times(coeff, Power(v,exp)) if(v == x) =>
        Times(coeff, Power(v, Minus(exp, Number(1))))
      case Times(coeff, v:Variable) if(v==x) => coeff
      case v:Variable if(v==x) => Number(1)
      case t:Term => t
    })

    /* construct the arguments ti diff aux:
     * y' = -xPrimeDividedByX/2 * y
     * x=0 <-> \exists y x*y^2=0 & y>0 */
    //@todo At some point I was not sure if this works for no exponent (i.e. x, x+x, x+x+x and so on b/c of the pattern matching in dgZero. But it does. So review dgZero and this to see what's up.
    val (ghostODE, ghostEqn) = (
      AtomicODE(DifferentialSymbol(ghostVar), Times(Times(negOneHalf,xPrimeDividedByX) , ghostVar)),
      And(
        Equal(
          Times(x, Power(ghostVar, Number(2)) ),
          Number(0)
        ),
        Greater(ghostVar, Number(0))
      )
    )

    dG(ghostODE, Some(ghostEqn))(pos) & boxAnd(pos ++ PosInExpr(0::Nil)) &
      DifferentialTactics.diffInd()(pos ++ PosInExpr(0::0::Nil)) &
      //@note would be more robust to do the actual derivation here the way it's done in [[AutoDGTests]], but I'm leaving it like this so that we can find the bugs/failures in DGauto
      DGauto(pos ++ PosInExpr(0::1::Nil)) & QE & done
  })

  /** Proves properties of the form {{{x=0&n>0 -> [{x^n}]x=0}}}
    * @todo make this happen by usubst. */
  def dgZeroMonomial : DependentPositionTactic = "dgZeroMonomial" by ((pos: Position, seq:Sequent) => {
    if (ToolProvider.algebraTool().isEmpty) throw new BelleThrowable(s"dgZeroEquilibrium requires a AlgebraTool, but got None")

    val Some(Box(ODESystem(system, constraint), property)) = seq.sub(pos)

    /** The lhs of the post-condition {{{lhs = 0}}} */
    val lhs = property match {
      case Equal(term, Number(n)) if n == 0 => term
      case _ => throw new BelleThrowable(s"Not sure what to do with shape ${seq.sub(pos)}")
    }

    /** The equation in the ODE of the form {{{x'=c*x^n}}}; the n is optional.
      * @todo make this tactic work for systems of ODEs. */
    val (x: Variable, (c: Option[Term], n: Option[Term])) = system match {
      case AtomicODE(variable, equation) => (variable.x, equation match {
        case Times(c, Power(variable, n)) => (Some(c), Some(n))
        case Times(c, v:Variable) if v==variable.x => (Some(c), None)
        case Power(variable, n) => (None, Some(n))
        case v:Variable if v==variable.x => (None, None)
      })
    }
    require(lhs == x, "Currently require that the post-condition is of the form x=0 where x is the primed variable in the ODE.")

    /** The ghost variable */
    val ghostVar = "z_".asVariable
    require(!StaticSemantics.vars(system).contains(ghostVar), "fresh ghost " + ghostVar + " in " + system.prettyString) //@todo should not occur anywhere else in the sequent either...


    val (newOde: DifferentialProgram, equivFormula: Formula) = (c,n) match {
      case (Some(c), Some(n)) => (
        s"$ghostVar' = ( (-1*$c * $x^($n-1)) / 2) * $ghostVar + 0".asDifferentialProgram,
        s"$x*$ghostVar^2=0&$ghostVar>0".asFormula
      )
      case (None, Some(n)) => (
        s"$ghostVar' = ((-1*$x^($n-1)) / 2) * $ghostVar + 0".asDifferentialProgram,
        s"$x*$ghostVar^2=0&$ghostVar>0".asFormula
      )
      case (Some(c), None) => (
        s"$ghostVar' = ((-1*$c*$x) / 2) * $ghostVar + 0".asDifferentialProgram,
        s"$x*$ghostVar^2=0&$ghostVar>0".asFormula
      )
      case (None, None) => (
        s"$ghostVar' = -1 * $ghostVar + 0".asDifferentialProgram,
        s"$x * $ghostVar = 0 & $ghostVar > 0".asFormula
      )
    }

    val backupTactic = dG(newOde, Some(equivFormula))(pos) & boxAnd(pos ++ PosInExpr(0::Nil)) &
      DifferentialTactics.diffInd()(pos ++ PosInExpr(0::0::Nil)) &
      //@note would be more robust to do the actual derivation here the way it's done in [[AutoDGTests]], but I'm leaving it like this so that we can find the bugs/failures in DGauto
      DGauto(pos ++ PosInExpr(0::1::Nil)) & QE & done

    //@todo massage the other cases into a useAt.
    //@note it's more robust if we do the | backupTactic, but I'm ignore thins so that we can find and fix the bug in (this use of) useAt.
    if(c.isDefined && n.isDefined) //if has correct shape for using the derived axiom
      TactixLibrary.useAt("dgZeroEquilibrium")(1) //| backupTactic
    else
      backupTactic
  })

  /**
    * Proves Darboux properties
    * p = 0 -> [ {ODE & Q} ] p = 0
    * where Q -> p' = q p
    * (similarly for >= 0, > 0, != 0)
    * Note: this also works for fractional q, if its denominator is already in Q
    * Otherwise, DG will fail on the singularity
    * Note: this assumes that the (in)equalities are normalized to have 0 on the RHS
    * Rationale: this tactic requires a cofactor input, and so it would be surprising if it normalizes internally
    * All automation tactics around dgDbx will need to normalize their input
    */
  def dgDbx(qco: Term): DependentPositionWithAppliedInputTactic = "dbx" byWithInput (qco, (pos: Position, seq:Sequent) => {
    require(pos.isSucc && pos.isTopLevel, "dbx only at top-level succedent")

    val (system,property) = seq.sub(pos) match {
      case Some (Box (ODESystem (system, _), property) ) => (system,property)
      case _ => throw new BelleThrowable(s"dbx only at box ODE in succedent")
    }

    /** The argument works for any comparison operator */
    val (p,pop) = property match {
      case bop:ComparisonFormula if bop.right.isInstanceOf[Number] && bop.right.asInstanceOf[Number].value == 0 =>
        (bop.left,bop)
      case _ => throw new BelleThrowable(s"Not sure what to do with shape ${seq.sub(pos)}, dgDbx requires 0 on RHS")
    }

    val isOpen = property match {
      case  _: Greater => true
      case _: Less => true
      case _ => false
    }

    //Skip ghosts if input cofactor was just 0
    //Could also do more triviality checks like -0, 0+0 etc.
    if (qco == Number(0)) {
      //println("dgDbx automatically used dI for trivial cofactor")
      if(isOpen) openDiffInd(pos) else dI('full)(pos)
    }
    else {
      /** The ghost variable */
      val gvy = "dbxy_".asVariable
      require(!StaticSemantics.vars(system).contains(gvy), "fresh ghost " + gvy + " in " + system.prettyString)
      //@todo should not occur anywhere else in the sequent either...

      /** Another ghost variable */
      val gvz = "dbxz_".asVariable
      require(!StaticSemantics.vars(system).contains(gvz), "fresh ghost " + gvz + " in " + system.prettyString)
      //@todo should not occur anywhere else in the sequent either...

      //Construct the diff ghost y' = -qy
      val dey = AtomicODE(DifferentialSymbol(gvy), Times(Neg(qco), gvy))
      //Diff ghost z' = qz/2
      val dez = AtomicODE(DifferentialSymbol(gvz), Times(Divide(qco, Number(2)), gvz))

      val zero = Number(0)
      val one = Number(1)
      val two = Number(2)

      //Postcond:
      //For equalities, != 0 works too, but the > 0 works for >=, > as well
      val gtz = Greater(gvy, zero)
      val pcy = And(gtz, pop.reapply(Times(gvy, p), zero))
      val pcz = Equal(Times(gvy, Power(gvz, two)), one)

      DebuggingTactics.debug("Darboux postcond " + pcy.toString + " " + pcz.toString) &
        dG(dey, Some(pcy))(pos) & //Introduce the dbx ghost
        existsR(one)(pos) & //Anything works here, as long as it is > 0, 1 is convenient
        diffCut(gtz)(pos) < (
          boxAnd(pos) & andR(pos) < (
            dW(pos) & prop,
            if (isOpen) openDiffInd(pos) else diffInd('full)(pos)
          ) // Closes p z = 0 invariant
          ,
          dG(dez, Some(pcz))(pos) & //Introduce the dbx ghost
            existsR(one)(pos) & //The sqrt inverse of y, 1 is convenient
            diffInd('full)(pos) // Closes z > 0 invariant with another diff ghost
        )
    }
  })

  /**
    * This tactic is EXPERIMENTAL: it requires the use of max in a ghost
    * Proves a strict barrier certificate property
    * p >~ 0 -> [ {ODE & Q} ] p >~ 0
    * where Q & p = 0 -> p' > 0
    * works for both > and >= (and <, <=)
    * Soundness note: this uses a ghost that is not smooth
    */
  private val maxF = Function("max", None, Tuple(Real, Real), Real, interpreted=true)
  private val minF = Function("min", None, Tuple(Real, Real), Real, interpreted=true)

  private lazy val barrierCond: ProvableSig = remember("max(f_()*f_(),g_()) > 0 <-> f_()=0 -> g_()>0".asFormula,QE,namespace).fact

  def dgBarrier(tool: Option[SimplificationTool] = None): DependentPositionTactic = "barrier" by ((pos: Position, seq:Sequent) => {
    require(pos.isSucc && pos.isTopLevel, "barrier only at top-level succedent")

    val (system,dom,post) = seq.sub(pos) match {
      case Some (Box (ODESystem (system, dom), property) ) => (system,dom,property)
      case _ => throw new BelleThrowable(s"barrier only at box ODE in succedent")
    }

    val (property,propt)= ineqNormalize(post)

    val starter = propt match {
      case None => skip
      case Some(pr) => useAt(pr)(pos ++ PosInExpr(1::Nil))
    }

    //p>=0 or p>0
    val barrier = property.asInstanceOf[ComparisonFormula].left

    val lie = DifferentialHelper.simplifiedLieDerivative(system, barrier, tool)

    val zero = Number(0)
    //The special max term
    val barrierAlg = FuncOf(maxF,Pair(Times(barrier,barrier),lie))
    val barrierFml = Greater(barrierAlg,zero)
    //The cofactor
    val cofactor = Divide(Times(barrier,lie),barrierAlg)

    // First cut in the barrier property, then use dgdbx on it
    // Barrier condition is checked first to make it fail faster
    dC(barrierFml)(pos) <(
      skip, /* diffWeakenG faster but loses assumptions */ dW(pos) & useAt(barrierCond)(1,1::Nil) & timeoutQE & done
    ) & starter & dgDbx(cofactor)(pos)
  })

  /** Find Q|- p' = q p + r, and proves |- Q -> r~0 with appropriate
    * sign condition on r as specified by "property"
    * In addition, if the "property" was open, then also assume it in Q
    */
  private [btactics] def findDbx(ode: DifferentialProgram, dom: Formula,
                                 property: ComparisonFormula, strict:Boolean=true): (ProvableSig,Term,Term) = {

    val p = property.left
    val lie = DifferentialHelper.simplifiedLieDerivative(ode, p, ToolProvider.simplifierTool())
    // p' = q p + r
    val (q,r) = domQuoRem(lie,p,dom)
    val zero = Number(0)

    //The sign of the remainder for a Darboux argument
    //e.g., tests r >= 0 for p'>=gp (Darboux inequality)
    val pr = property match {
      case GreaterEqual(_, _) => proveBy(Imply(dom,GreaterEqual(r,zero)),timeoutQE)
      case Greater(_, _) => proveBy(Imply(And(dom,property),GreaterEqual(r,zero)),timeoutQE)
      case LessEqual(_, _) => proveBy(Imply(dom,LessEqual(r,zero)),timeoutQE)
      case Less(_, _) => proveBy(Imply(And(dom,property),LessEqual(r,zero)),timeoutQE)
      case Equal(_,_) => proveBy(Imply(dom,Equal(r,zero)),timeoutQE)
      //todo: is there a special case of open DI that would work for disequalities?
      case NotEqual(_,_) => proveBy(Imply(dom,Equal(r,zero)),timeoutQE)
      case _ => throw new BelleThrowable(s"Darboux only on atomic >,>=,<,<=,!=,= postconditions")
    }

    if(pr.isProved)
      return (pr,q,r)
    if(q != Number(0)) {
      // Fall-back check if straightforward DI would work
      // This is needed, because one can e.g. get p'>=0 without having r>=0 when domain constraints are possible
      // todo: is it possible to improve the Darboux (in)equality generation heuristic to automatically cover this case?
      val pr = property match {
        case GreaterEqual(_, _) => proveBy(Imply(dom,GreaterEqual(lie,zero)),timeoutQE)
        case Greater(_, _) => proveBy(Imply(And(dom,property),GreaterEqual(lie,zero)),timeoutQE)
        case LessEqual(_, _) => proveBy(Imply(dom,LessEqual(lie,zero)),timeoutQE)
        case Less(_, _) => proveBy(Imply(And(dom,property),LessEqual(lie,zero)),timeoutQE)
        case Equal(_,_) => proveBy(Imply(dom,Equal(lie,zero)),timeoutQE)
        //todo: is there a special case of open DI that would work for disequalities?
        case NotEqual(_,_) => proveBy(Imply(dom,Equal(lie,zero)),timeoutQE)
        case _ => throw new BelleThrowable(s"Darboux only on atomic >,>=,<,<=,!=,= postconditions")
      }
      if(pr.isProved)
        return (pr,Number(0),lie)
    }

    if(strict)
      throw new BelleThrowable("Automatic darboux failed -- poly :"+p+" lie: "+lie+" cofactor: "+q+" rem: "+r+" unable to prove: "+pr.conclusion)

    (pr,q,r)
  }

  // Normalises to p = 0 then attempts to automatically guess the darboux cofactor
  def dgDbxAuto: DependentPositionTactic = "dbx" by ((pos: Position, seq:Sequent) => {
    require(pos.isSucc && pos.isTopLevel, "dgDbxAuto only at top-level succedent")

    val (system,dom,post) = seq.sub(pos) match {
      case Some (Box (ODESystem (system, dom), property) ) => (system,dom,property)
      case _ => throw new BelleThrowable(s"dbx auto only at box ODE in succedent")
    }

    val (property,propt) = atomNormalize(post)

    val starter = propt match {
      case None => skip
      case Some(pr) => useAt(pr)(pos ++ PosInExpr(1::Nil))
    }

    //normalized to have p on LHS
    //todo: utilize pr which proves the necessary sign requirement for denRemReq
    val (pr,cofactor,rem) = findDbx(system,dom,property.asInstanceOf[ComparisonFormula])

    starter & dgDbx(cofactor)(pos)
  })

  /** @see [[TactixLibrary.DGauto]]
    * @author Andre Platzer */
  def DGauto: DependentPositionTactic = "DGauto" by ((pos:Position,seq:Sequent) => {
    if (ToolProvider.algebraTool().isEmpty) throw new BelleThrowable("DGAuto requires a AlgebraTool, but got None")
    /** a-b with some simplifications */
    def minus(a: Term, b: Term): Term = b match {
      case Number(n) if n == 0 => a
      case _ => a match {
        case Number(n) if n == 0 => Neg(b)
        case _ => Minus(a, b)
      }
    }
    val (quantity: Term, ode: DifferentialProgram) = seq.sub(pos) match {
      case Some(Box(ODESystem(o, _), Greater(a, b))) => (minus(a, b), o)
      case Some(Box(ODESystem(o, _), Less(a, b))) => (minus(b, a), o)
      case e => throw new BelleThrowable("DGauto does not support argument shape: " + e)
    }
    //@todo find a ghost that's not in ode
    val ghost: Variable = Variable("y_")
    require(!StaticSemantics.vars(ode).contains(ghost), "fresh ghost " + ghost + " in " + ode)
    // [x':=f(x)](quantity)'
    val lie = DifferentialHelper.lieDerivative(ode, quantity)

    lazy val constrGGroebner: Term = {
      val groebnerBasis: List[Term] = ToolProvider.algebraTool().getOrElse(throw new BelleThrowable("DGAuto requires an AlgebraTool, but got None")).groebnerBasis(
        quantity :: Nil)
      ToolProvider.algebraTool().getOrElse(throw new BelleThrowable("DGAuto requires an AlgebraTool, but got None")).polynomialReduce(
        lie match {
          case Minus(Number(n), l) if n == 0 => l //@note avoid negated ghost from (f()-x)'
          case _ => lie
        },
        groebnerBasis.map(Times(Number(-2), _))
      )._1.head
    }

    val odeBoundVars = StaticSemantics.boundVars(ode).symbols[NamedSymbol].toList.filter(_.isInstanceOf[BaseVariable]).sorted.map(_.asInstanceOf[BaseVariable])
    val constrG: Term = ToolProvider.algebraTool().getOrElse(throw new BelleThrowable("DGAuto requires an AlgebraTool, but got None")).quotientRemainder(
      lie, Times(Number(-2), quantity), odeBoundVars.headOption.getOrElse(Variable("x")))._1

    // Formula that must be valid: quantity <-> \exists ghost. quantity * ghost^2 > 0
    // Ghosted-in differential equation: ghost' = constrG*ghost + 0
    def dg(g: Term): BelleExpr = {
      val de = AtomicODE(DifferentialSymbol(ghost), Plus(Times(g, ghost), Number(0)))
      val p = Greater(Times(quantity, Power(ghost, Number(2))), Number(0))
      DebuggingTactics.debug(s"DGauto: trying $de with $p") &
      dG(de,Some(p))(pos) & diffInd()(pos ++ PosInExpr(0::Nil)) & QE & done
    }

    // try guessing first, groebner basis if guessing fails
    dg(constrG) | TacticFactory.anon((seq: Sequent) => dg(constrGGroebner))
  })

  /** Search-and-rescue style DGauto.
    * @author Andre Platzer
    */
  def DGautoSandR: DependentPositionTactic = "DGauto" by ((pos:Position,seq:Sequent) => {
    if (!ToolProvider.solverTool().isDefined) throw new BelleThrowable("DGAuto requires a SolutionTool, but got None")
    /** a-b with some simplifications */
    def minus(a: Term, b: Term): Term = b match {
      case Number(n) if n==0 => a
      case _ => a match {
        case Number(n) if n==0 => Neg(b)
        case _ => Minus(a,b)
      }
    }
    val (quantity: Term, ode: DifferentialProgram) = seq.sub(pos) match {
      case Some(Box(ODESystem(ode, _), Greater(a, b))) => (minus(a,b), ode)
      case Some(Box(ODESystem(ode, _), Less(a, b))) => (minus(b,a), ode)
      case e => throw new BelleThrowable("DGauto does not support argument shape: " + e)
    }
    //@todo find a ghost that's not in ode
    val ghost: Variable = Variable("y_")
    require(!StaticSemantics.vars(ode).contains(ghost), "fresh ghost " + ghost + " in " + ode)
    val spooky: Term = if (false) //@todo ultimate substitution won't work if it ain't true. But intermediate semantic renaming won't work if it's false.
      UnitFunctional("jj",Except(ghost),Real)
    else
      FuncOf(Function("jj",None,Unit,Real),Nothing) //Variable("jj")
    //@todo should allocate space maybe or already actually by var in this lambda
    var constructedGhost: Option[Term] = None
    // proper search & rescue tactic
    val SandR: BelleExpr = LetInspect(
      spooky,
      (pr:ProvableSig) => {
        assume(pr.subgoals.length==1, "exactly one subgoal from DA induction step expected")
        logger.debug("Instantiate::\n" + pr)
        // induction step condition \forall x \forall ghost condition>=0
        val condition = FormulaTools.kernel(pr.subgoals.head.succ.head) match {
          case Imply(domain, GreaterEqual(condition, Number(n))) if n==0 => condition
          case GreaterEqual(condition, Number(n)) if n==0 => condition
          case _ => throw new AssertionError("DGauto: Unexpected shape " + pr)
        }
        //@todo a witness of Reduce of >=0 would suffice
        logger.debug("Solve[" + condition + "==0" + "," + spooky + "]")
        ToolProvider.solverTool().getOrElse(throw new BelleThrowable("DGAuto requires a SolutionTool, but got None")).solve(Equal(condition, Number(0)), spooky::Nil) match {
          case Some(Equal(l,r)) if l==spooky => logger.debug("Need ghost " + ghost + "'=(" + r + ")*" + ghost + " for " + quantity)
            constructedGhost = Some(r)
            r
          case None => logger.debug("Solve[" + condition + "==0" + "," + spooky + "]")
            throw new BelleThrowable("DGauto could not solve conditions: " + condition + ">=0")
          case Some(stuff) => logger.debug("Solve[" + condition + "==0" + "," + spooky + "]")
            throw new BelleThrowable("DGauto got unexpected solution format: " + condition + ">=0\n" + stuff)
        }
      }
      ,
      dG(AtomicODE(DifferentialSymbol(ghost), Plus(Times(spooky, ghost), Number(0))),
        Some(Greater(Times(quantity, Power(ghost,Number(2))), Number(0)))
      )(pos) & diffInd()(pos ++ PosInExpr(0::Nil))
    ) & QE & done
    // fallback rescue tactic if proper misbehaves
    val fallback: DependentPositionTactic = "ANON" by ((pos:Position,seq:Sequent) => {
      logger.debug("DGauto falling back on ghost " + ghost + "'=(" + constructedGhost + ")*" + ghost)
      // terrible hack that accesses constructGhost after LetInspect was almost successful except for the sadly failing usubst in the end.
      dG(AtomicODE(DifferentialSymbol(ghost), Plus(Times(constructedGhost.getOrElse(throw new BelleThrowable("DGauto construction was unsuccessful in constructing a ghost")), ghost), Number(0))),
        Some(Greater(Times(quantity, Power(ghost, Number(2))), Number(0)))
      )(pos) <(
        QE & done,
        //@todo could optimize for RCF cache when doing the same decomposition as during SandR
        //diffInd()(pos ++ PosInExpr(1::Nil)) & QE
        implyR(pos) & diffInd()(pos) & QE & done
        )
    })
    SandR | fallback(pos)
  })

  /** Pieces together some ODE invariance tactics into a prover for ODE invariance:
    *
    * G |- P   P|-[x'=f(x)&Q]P
    * ---
    * G |- [x'=f(x)&Q]P
    *
    * @param tryHard configures how hard the tactic tries to prove invariance in particular
    *                use tryHard = true when speed is secondary & certain that P is invariant
    *                use tryHard = false when speed is of interest e.g., within automated invariant search
    */
  def odeInvariant(tryHard: Boolean = false, useDw: Boolean = true): DependentPositionTactic = "odeInvariant" by ((pos:Position) => {
    require(pos.isSucc && pos.isTopLevel, "ODE invariant only applicable in top-level succedent")
    //@note dW does not need algebra tool
    //require(ToolProvider.algebraTool().isDefined,"ODE invariance tactic needs an algebra tool (and Mathematica)")

    val invTactic =
      if(tryHard)
      {
        ODEInvariance.sAIclosedPlus(bound = 3)(pos) |
        //todo: duplication currently necessary between sAIclosedPlus and sAIclosed due to unresolved Mathematica issues
        ODEInvariance.sAIclosed(pos) |
        ODEInvariance.sAIRankOne(doReorder = true, skipClosed = false)(pos)
      }
      else {
        ODEInvariance.sAIclosedPlus(bound = 1)(pos) |
        ODEInvariance.sAIRankOne(doReorder = false, skipClosed = true)(pos)
      }

    //Add constant assumptions to domain constraint
    SaturateTactic(andL('L)) & //Safe because pos is guaranteed to be in the succedent
    DifferentialTactics.DconstV(pos) &
    //Naive simplification of postcondition with domain constraint
    DifferentialTactics.domSimplify(pos) &
    DebuggingTactics.debug("odeInvariant close") &
    (
      if (useDw) {
        (DifferentialTactics.diffWeakenG(pos) & timeoutQE & done) |
          invTactic |
          DebuggingTactics.error("odeInvariant failed to prove postcondition invariant for ODE. Try using a differential cut to refine the domain constraint first.")
      } else {
        invTactic |
          DebuggingTactics.error("odeInvariant failed to prove postcondition invariant for ODE. Try using a differential cut to refine the domain constraint first.")
      }
    )
  })

  // Asks Pegasus invariant generator for an invariant (DC chain)
  // Try hard to prove G|-[x'=f(x)&Q]P by an invariance argument with the chain only (NO SOLVE)
  lazy val odeInvariantAuto : DependentPositionTactic = "odeInvariant" by ((pos:Position, seq: Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "ODE invariant (with Pegasus) only applicable in top-level succedent")
    require(ToolProvider.algebraTool().isDefined,"ODE invariance tactic needs an algebra tool (and Mathematica)")

    SaturateTactic(andL('L)) & //Safe because pos is guaranteed to be in the succedent
    DifferentialTactics.DconstV(pos) & odeInvariantAutoBody(pos)
  })

  private def odeInvariantAutoBody: DependentPositionTactic = "ANON" by ((pos:Position,seq:Sequent) => {
    val invs = InvariantGenerator.pegasusInvariants(seq,pos).toList
    //Empty list = failed to generate an invariant
    //True ~ no DCs needed
    //Else, DC chain
    // Assume that Pegasus hands us back a diffcut chain
    invs.headOption match {
      case None => throw new BelleThrowable(s"Pegasus failed to generate an invariant")
      case Some((True, _)) => diffWeakenG(pos) & timeoutQE & done
      case _ =>
        invs.foldRight(diffWeakenG(pos) & timeoutQE & done)( (fml,tac) =>
          //DebuggingTactics.print("DC chain: "+fml) &
          DC(fml._1)(pos) <(tac,
            (
            //note: repeated dW&QE not needed if Pegasus reports a correct dC chain
            //(DifferentialTactics.diffWeakenG(pos) & QE & done) |
            ODEInvariance.sAIclosedPlus(bound=1)(pos) |
            ODEInvariance.sAIRankOne(doReorder=false,skipClosed = true)(pos)) & done)
        )
    }
  })

  // implementation helpers

  /** Computes quotient remainder resulting from (RATIONAL) polynomial division wrt equalities in domain
    * @param poly polynomial to divide
    * @param div divisor
    * @param dom domain constraint
    * @return (q,r) where Q |- poly = q*div + r , q,r are polynomials
    */
  def domQuoRem(poly: Term, div: Term, dom: Formula): (Term,Term) = {
    //TODO: remove dependence on algebra tool
    if (ToolProvider.algebraTool().isEmpty) {
      throw new BelleThrowable(s"duoQuoRem requires a AlgebraTool, but got None")
      // val polynorm = PolynomialArith.normalise(poly,true)._1
      // val divnorm = PolynomialArith.normalise(div,true)._1
    }
    else {
      val algTool = ToolProvider.algebraTool().get
      val gb = algTool.groebnerBasis(domainEqualities(dom))
      val quo = algTool.polynomialReduce(poly, div :: gb)
      // quo._1.head is the cofactor of div (q)
      // quo._2 is the remainder (r)

      (quo._1.head,quo._2)
      //Older support for rational functions
      //val (g, q) = stripDenom(quo._1.head)
      //if ((FormulaTools.singularities(g) ++ FormulaTools.singularities(q)).isEmpty) (g, q, quo._2)
      //else (Number(0), Number(1), poly)
    }
  }

  //Keeps equalities in domain constraint
  private[btactics] def domainEqualities(f:Formula) : List[Term] = {
    flattenConjunctions(f).flatMap{
      case Equal(l,r) => Some(Minus(l,r))
      case _ => None
    }
  }

  /** Indicates whether there is an ODE at the indicated position of a sequent */
  val isODE: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(_: ODESystem, _))     => true
      case Some(Diamond(_: ODESystem, _)) => true
      case Some(e) => false
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Indicates whether there is a proper ODE System at the indicated position of a sequent with >=2 ODEs */
  val isODESystem: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(ODESystem(_:DifferentialProduct,_), _))     => true
      case Some(Diamond(ODESystem(_:DifferentialProduct,_), _)) => true
      case Some(e) => false
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Computes the dimension of ODE at indicated position of a sequent */
  private[btactics] val getODEDim: (Sequent,Position)=>Int = (sequent,pos) => {
    def odeDim(ode: ODESystem): Int = StaticSemantics.boundVars(ode).symbols.count(_.isInstanceOf[DifferentialSymbol])
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _))     => odeDim(ode)
      case Some(Diamond(ode: ODESystem, _)) => odeDim(ode)
      case Some(e) => throw new IllegalArgumentException("no ODE at position " + pos + " in " + sequent + "\nFound: " + e)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Whether the ODE at indicated position of a sequent has a nontrivial domain */
  val hasODEDomain: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _))     => ode.constraint != True
      case Some(Diamond(ode: ODESystem, _)) => ode.constraint != True
      case Some(e) => throw new IllegalArgumentException("no ODE at position " + pos + " in " + sequent + "\nFound: " + e)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Flattens a formula to a list of its top-level conjunctions */
  def flattenConjunctions(f: Formula): List[Formula] = {
    var result: List[Formula] = Nil
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preF(p: PosInExpr, f: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = f match {
        case And(l, r) => result = result ++ flattenConjunctions(l) ++ flattenConjunctions(r); Left(Some(ExpressionTraversal.stop))
        case a => result = result :+ a; Left(Some(ExpressionTraversal.stop))
      }
    }, f)
    result
  }

  // TODO: these Lemmas are just the symmetric versions of some DerivedAxioms.
  // Using PosInExpr(1::Nil) as key in chaseCustom does not seem to work.
  private lazy val minPosAnd = remember("min(f_(), g_())>0<->f_()>0 & g_()>0".asFormula, QE & done)
  private lazy val minNonnegAnd = remember("min(f_(), g_())>=0<->f_()>=0 & g_()>=0".asFormula, QE & done)
  private lazy val maxPosOr = remember("max(f_(), g_())>0<->f_()>0 | g_()>0".asFormula, QE & done)
  private lazy val maxNonnegOr = remember("max(f_(), g_())>=0<->f_()>=0 | g_()>=0".asFormula, QE & done)
  private lazy val minusPos = remember("f_()-g_()>0 <-> f_()>g_()".asFormula, QE & done)
  private lazy val minusNonneg = remember("f_()-g_()>=0 <-> f_()>=g_()".asFormula, QE & done)
  /** chases min/max Less/LessEqual 0 to conjunctions and disjunctions */
  val chaseMinMaxInequalities : DependentPositionTactic = chaseCustom({
    case Greater(FuncOf(m, _), Number(n)) if m == minF =>
      (minPosAnd.fact, PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)::Nil
    case GreaterEqual(FuncOf(m, _), Number(n)) if m == minF =>
      (minNonnegAnd.fact, PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)::Nil
    case Greater(FuncOf(m, _), Number(n)) if m == maxF =>
      (maxPosOr.fact, PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)::Nil
    case GreaterEqual(FuncOf(m, _), Number(n)) if m == maxF =>
      (maxNonnegOr.fact, PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)::Nil
    case _ => Nil
  })

  private def interiorImplication: DependentTactic = "ANON" by { (seq: Sequent) =>
    require (seq.succ.length == 1)
    require (seq.ante.length == 1)
    (seq.ante(0), seq.succ(0)) match {
      case (And(p, q), And(r, s)) =>
        andL(-1) & andR(1) & Idioms.<(
          hideL(-2) & interiorImplication,
          hideL(-1) & interiorImplication
        )
      case (Or(p, q), Or(r, s)) =>
        orR(1) & orL(-1) & Idioms.<(
          hideR(2) & interiorImplication,
          hideR(1) & interiorImplication
        )
      case (Less(a, b), LessEqual(c, d)) if a == c && b == d => useAt("<=")(1) & orR(1) & closeId
      case (Greater(a, b), GreaterEqual(c, d)) if a == c && b == d => useAt(">=")(1) & orR(1) & closeId
      case (False, _) => closeF
      case (x, y) if x == y => closeId
      case _ =>
        throw new BelleThrowable("strengthenInequalities expected ante and succ of same shape, but got " + seq)
    }
  }

  /**
    * Strengthens the postcondition to its interior and cuts in its closure
    * (provided the closure holds initially).
    *
    * G |- [{ode&p&closure(q)}]interior(q)           G |- closure(q)
    * ----------------------------------------------------------------dCClosure
    * G |- [{ode&p}]q
    *
    * interior(q) and closure(q) are wrt. to the negation normal form (NNF) of q
    * @see [[FormulaTools.interior]]
    * @see [[FormulaTools.closure]]
    *
    */
  val dCClosure: DependentPositionTactic = "dCClosure" by ((pos:Position,seq: Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "dCClosure expects to be called on top-level succedent")

    val (ode,p_fml,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,p)) => (sys.ode,sys.constraint,p)
      case _ => throw new BelleThrowable("dCClosure expects succedent of shape [{ode&p}]q")
    }

    val (q_fml, propt) = semiAlgNormalize(post)

    /* Apply the semialg normalization step */
    val starter = propt.map(pr => useAt(pr)(pos ++ PosInExpr(1 :: Nil))).getOrElse(skip)

    val interior = FormulaTools.interior(q_fml)
    val closure = FormulaTools.closure(q_fml)

    val (mm_fmlGt, proptGt) = maxMinGtNormalize(interior)
    val (mm_fmlGe, proptGe) = maxMinGeqNormalize(closure)

    //NOTE: mm_fmlGt should be identical to mm_fmlGe except with > instead of >=

    /* Apply/Undo the max-min normalization steps */

    val (maxminGt, backGt) = proptGt match {
      case None => (skip, skip)
      case Some(pr) => (useAt(pr)(pos ++ PosInExpr(1 :: Nil)), useAt(pr, PosInExpr(1 :: Nil))(pos ++ PosInExpr(1 :: Nil)))
    }

    val (backGe1, backGe2) = proptGe match {
      case None => (skip, skip)
      case Some(pr) => (useAt(pr, PosInExpr(1 :: Nil))(pos ++ PosInExpr(0::1::1:: Nil)), useAt(pr, PosInExpr(1 :: Nil))(pos))
    }

    // TODO: several of these local tactics might be useful in a more general setting
//    def interiorPostBox = "ANON" by { (seq: Sequent) =>
//      require (seq.succ.length == 1)
//      seq.succ(0) match {
//        case Box(a, post) =>
//          generalize(FormulaTools.interior(post))(1) & Idioms.<(skip,
//            cohideOnlyL('Llast) & interiorImplication
//          )
//        case x =>
//          throw new BelleThrowable("interiorPostcondition expected a Box but got " + x)
//      }
//    }
//    def normalizeAt(nrmlz : Formula => (Formula,Option[ProvableSig])) : DependentPositionTactic = "ANON" by { (pos: Position, seq: Sequent) =>
//      seq.sub(pos) match {
//        case Some(fml: Formula) =>
//          nrmlz(fml) match {
//            case (a, Some(prv)) =>
//              useAt(prv)(pos)
//            case _ =>
//              skip
//          }
//        case x =>
//          throw new BelleThrowable("normalizeAt expected Some Formula but got " + x)
//      }
//    }

    /* cut right subgoal */
    starter &
    cutR(closure)(pos) <(
      skip,
      // Turn postcondition into interior
      implyR(pos) & generalize(interior)(pos) <(
        maxminGt & useAt("open invariant closure >")(pos) <(
          backGt & backGe1 & hideL('Llast),
          backGe2 & closeId
        ),
        cohideOnlyL('Llast) & interiorImplication
      )
    )
  })

  /**
    * assume closure of postcondition for proof of invariant interior
    *
    * G, p |- [{ode&p}](closure(q)->(interior(q))')          G |- interior(q)
    * ------------------------------------------------------------------------dIClosure
    * G |- [{ode&p}]q
    *
    * interior(q) and closure(q) are wrt. to the negation normal form (NNF) of q
    * @see [[FormulaTools.interior]]
    * @see [[FormulaTools.closure]]
    *
    */
  val dIClosure: DependentPositionTactic = "dIClosure" by ((pos:Position,seq: Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "dIClosure expects to be called on top-level succedent")

    val (ode,p_fml,post) = seq.sub(pos) match {
      case Some(Box(sys:ODESystem,p)) => (sys.ode,sys.constraint,p)
      case _ => throw new BelleThrowable("dIClosure expects succedent of shape [{ode&p}]q")
    }

    val (q_fml, propt) = semiAlgNormalize(post)
    /* Apply the semialg normalization step */
    val starter = propt.map(pr => useAt(pr)(pos ++ PosInExpr(1 :: Nil))).getOrElse(skip)

    val interior = FormulaTools.interior(q_fml)

    val closure = FormulaTools.closure(q_fml)

    starter &
    cutR(interior)(pos) <(
      skip, //QE
      implyR(1) &
      dCClosure(pos) <(
        cohide2(AntePosition(seq.ante.length+1),pos) & interiorImplication,
        //dI('full)(pos)
        DI(pos) & implyR(pos) & andR(pos) <(
          closeId,
          DW(pos) & diffRefine(p_fml)(pos) <(
            generalize(Imply(closure,DifferentialFormula(interior)))(pos) <(
              hideL(AntePosition(seq.ante.length+1)) & andL('Llast) & hideL('Llast),
              implyR(1) & andL('Llast) & implyL(-1) <(closeId, closeId)
            )
            ,
            diffWeakenG(pos) & implyR(1) & andL(-1) & closeId
          )
        )
      )
    )
  })
}
