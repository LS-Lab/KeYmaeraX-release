package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{DependentPositionTactic, IllFormedTacticApplicationException, SaturateTactic}
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas.remember
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.anon
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.infrastruct.Position
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._

/**
  * Provides support for generating switched system models
  * under various switching mechanisms.
  *
  * Also provides proof automation for stability proofs
  *
  */

object SwitchedSystems {

  private val namespace = "switchedsys"

  //An ADT encoding canonical formats for switched systems
  sealed trait SwitchedSystem {
    // Represent this switched system as a hybrid program
    // Using topt as the optional clock variable
    def asProgram(t : Variable) : Program
    def asProgram : Program

    val cvars : List[Variable] // the default continuous state variables
    val vars : List[Variable]  // any variable appearing anywhere in the system
  }

  // Unfold a choice of the form hp1++hp2++hp3 into a list (the order of association is important)
  private def choiceList(p : Program) : List[Program] = {
    p match {
      case Choice(o,rest) => o::choiceList(rest)
      case _  => List(p)
    }
  }

  // Unfold a compose of the form hp1;hp2;hp3 into a list (the order of association is important)
  private def composeList(p : Program) : List[Program] = {
    p match {
      case Compose(o,rest) => o::composeList(rest)
      case _  => List(p)
    }
  }

  /**  State dependent switching
    *  Switching between a list of ODEs (with domains)
    */
  case class StateDependent(odes: List[ODESystem]) extends SwitchedSystem {

    require(odes.nonEmpty, "State-dependent switched system requires at least 1 ODE")

    override def asProgram = asProgram(None)
    override def asProgram(t:Variable) = asProgram(Some(t))

    private def asProgram(topt: Option[Variable]) = {
      require(topt.isEmpty || !vars.contains(topt.get), "Time variable " + topt.get + " must be fresh")

      val todes: List[Program] = topt match {
        case None => odes
        case Some(t) =>
          odes.map(ode =>
            ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(t), Number(1)), ode.ode), ode.constraint))
      }

      // arbitrary switching choice is modeled by dL's ++
      val body = todes.reduceRight(Choice)

      // repeated switching is modeled by dL's *
      Loop(body)
    }

    override val cvars : List[Variable] = odes.map(ode => StaticSemantics.boundVars(ode).toSet.toList.filterNot(StaticSemantics.isDifferential(_))).flatten.distinct
    override val vars : List[Variable] = odes.map(ode => StaticSemantics.vars(ode).toSet.toList.filterNot(StaticSemantics.isDifferential(_))).flatten.distinct
  }

  // Remove the time variable
  private def stripTimer(odes:List[ODESystem], topt:Option[Variable]) : List[ODESystem] = {
    topt match {
      case None => odes
      case Some(t) =>
        val tode = AtomicODE(DifferentialSymbol(t), Number(1))
        odes.map( ode =>
          ode.ode match {
            case DifferentialProduct(l,r) if l == tode => ODESystem(r,ode.constraint)
            case _ => throw new IllegalArgumentException("Unable to parse time variable " + t + " in ODE " + ode)
          }
        )
    }
  }

  def stateDependentFromProgram(p : Program, topt:Option[Variable] = None) : StateDependent = {
    p match {
      case Loop(choices) =>
        val odes = choiceList(choices)
        if(odes.forall(_.isInstanceOf[ODESystem]))
          StateDependent(stripTimer(odes.map(_.asInstanceOf[ODESystem]),topt))
        else
          throw new IllegalArgumentException("Unexpected program found in " + odes)
      case _ =>
        throw new IllegalArgumentException("Unable to parse program as state-dependent switched system " + p)
    }
  }

  /**  Controlled switching
    *  List of modes, where each mode consists of:
    *  name: String (represented as constant function name())
    *  ode: ODESystem (continuous dynamics of the mode with domain aka mode invariant)
    *  transitions: List[(Formula,List[Assign],Function)]
    *   - guard: Formula (transition guard)
    *   - reset: List[Assignment] (reset map, the resets happen IN ORDER, not simultaneously)
    *   - target: String (target mode)
    *
    *  ctrl: Variable (the variable to use as the control flag)
    *
    *  Note: this is the general structure for a hybrid automaton
    */
  case class Controlled(modes: List[(String,ODESystem,List[(String,Formula,List[Assign])])], u:Variable = Variable("u")) extends SwitchedSystem {

    // Explicit names of the modes
    val names : List[String] = modes.map(_._1)

    // Explicit ODEs of the modes
    val odes : List[ODESystem] = modes.map(_._2)

    // Explicit list of transitions
    val transitions: List[List[(String,Formula,List[Assign])]] = modes.map(_._3)

    override val cvars : List[Variable] = odes.map(ode => StaticSemantics.boundVars(ode).toSet.toList.filterNot(StaticSemantics.isDifferential(_))).flatten.distinct
    override val vars : List[Variable] =
      (odes.map(ode => StaticSemantics.vars(ode).toSet.toList.filterNot(StaticSemantics.isDifferential(_))).flatten ++
      transitions.flatten.map(t => (Test(t._2)::t._3).map(StaticSemantics.vars(_).toSet.toList).flatten).flatten).distinct

    // Some basic consistency checks
    require(modes.nonEmpty, "Controlled switching requires at least 1 mode")

    require(names.distinct.length == modes.length, "Controlled switching requires distinct names for each mode")

    require(!vars.contains(u), "Control variable " + u + " must be fresh")

    transitions.map(_.map( f =>
        require(names.contains(f._1), "Unable to jump to undefined mode: " + f._1)
    ))

    override def asProgram = asProgram(None)
    override def asProgram(t:Variable) = asProgram(Some(t))

    private def asProgram(topt: Option[Variable]) = {
      require(topt.isEmpty || !vars.contains(topt.get) && topt.get != u, "Time variable " + topt.get + " must be fresh")

      val todes: List[Program] = topt match {
        case None => odes
        case Some(t) =>
          odes.map(ode =>
            ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(t), Number(1)), ode.ode), ode.constraint))
      }

      // initializer
      val init = names.map( n => Assign(u,FuncOf(Function(n, None, Unit, Real), Nothing))).reduceRight(Choice)

      // control
      val trans = transitions.map(mt =>
        mt.map( f =>
          Compose((Test(f._2)::f._3).reduceRight(Compose), Assign(u,FuncOf(Function(f._1, None, Unit, Real), Nothing)))
        ).foldRight(Assign(u,u):Program)(Choice) //self loops
      )
      val ctrl = (names zip trans).map(np =>
        Compose(Test(Equal(u,FuncOf(Function(np._1, None, Unit, Real), Nothing))), np._2)).reduceRight(Choice)

      // plant
      val plant = (names zip todes).map(np =>
        Compose(Test(Equal(u,FuncOf(Function(np._1, None, Unit, Real), Nothing))), np._2)).reduceRight(Choice)

      // repeated switching is modeled by dL's *
      Compose(init,Loop(Compose(ctrl,plant)))
    }
  }

  private def parseInit(init : Program) : (Variable,List[String]) = {
    val choices = choiceList(init)
    if(!choices.forall(_.isInstanceOf[Assign]))
      throw new IllegalArgumentException("Unable to parse initializer for controlled switching "+init)
    val assigns = choices.map(c => c.asInstanceOf[Assign])
    val ctrl = assigns.map(f => f.x).distinct

    if(ctrl.length!=1)
      throw new IllegalArgumentException("Unable to parse initializer for controlled switching "+init)

    //todo: more precise check needed here
    val rhs = assigns.map(f=> f.e.asInstanceOf[FuncOf].func.name)
    (ctrl.head,rhs)
  }

  private def parsePlant(plant : Program) : (Variable,List[String],List[ODESystem]) = {
    val choices = choiceList(plant)

    val uvfo = choices.map( c => c match {
      case Compose(Test(Equal(uv:Variable, FuncOf(f, Nothing))), o: ODESystem) => (uv,f,o)
      case _ => throw new IllegalArgumentException("Unable to parse plant for controlled switching "+ plant)
    }
    )

    (uvfo.head._1,uvfo.map(_._2.name),uvfo.map(_._3))
  }

  private def parseCtrl(ctrl : Program) : (Variable,List[String],List[List[(String,Formula,List[Assign])]]) = {
    val choices = choiceList(ctrl)

    val uvfo = choices.map( c => c match {
      case Compose(Test(Equal(uv:Variable, FuncOf(f, Nothing))), o) => (uv,f,o)
      case _ => throw new IllegalArgumentException("Unable to parse ctrl for controlled switching "+ ctrl)
    }
    )

    val transitions = uvfo.map( f => {
      val tchoices = choiceList(f._3).dropRight(1)
      tchoices.map( tc => tc match {
        case Compose( Test(guard), Assign(_:Variable, FuncOf(f, Nothing)) ) =>
          (f.name,guard,Nil)
        case Compose( Compose(Test(guard),reset), Assign(_:Variable, FuncOf(f, Nothing)) ) =>
          (f.name,guard, composeList(reset).map(_.asInstanceOf[Assign]) )
        case _ => throw new IllegalArgumentException("Unable to parse ctrl for controlled switching "+ ctrl)
      })
      }
    )


    (uvfo.head._1,uvfo.map(_._2.name),transitions)
  }

  def controlledFromProgram(p : Program, topt:Option[Variable] = None) : Controlled = {
    p match {
      case Compose(init,Loop(Compose(ctrl,plant))) => {
        val (u1, modes1) = parseInit(init)
        val (u2, modes2, odes) = parsePlant(plant)
        val (u3, modes3, transitions) = parseCtrl(ctrl)

        // todo: more consistency checks
        // println(u1,modes1)
        // println(u2,modes2,odes)
        // println(u3,modes3,transitions)

        Controlled( (modes1,stripTimer(odes,topt),transitions).zipped.toList )
      }
      case _ =>
        throw new IllegalArgumentException("Unable to parse program for controlled switching " + p)
    }
  }

  /** Check that ODE's domain includes points that are about to locally exit or enter it under the dynamics of the ODE
    *
    * @note for closed domains, this is automatically true
    * @note returns an option with string and counterexample if it manages to find one
    * @param sys the ODE under consideration
    * @param dom the "global" domain of points to be considered
    */
  def odeActive(sys: ODESystem, dom: Formula = True): Option[(String, Map[NamedSymbol, Expression])] = {

    val odels = DifferentialProduct.listify(sys.ode).map {
      case AtomicODE(x, e) => (x, e)
      case _ => throw new IllegalArgumentException("ODE sanity checks can only be used on concrete ODEs.")
    }
    val oder = odels.map(xe => AtomicODE(xe._1, Neg(xe._2))).reduceRight(DifferentialProduct.apply)

    val (normalized, _) = try {
      SimplifierV3.semiAlgNormalize(sys.constraint)
    } catch {
      case ex: IllegalArgumentException =>
        throw new IllegalArgumentException("Unable to normalize domain to semi-algebraic format: " + sys.constraint, ex)
    }

    //Points about to enter ODE domain under ODE dynamics
    val fwdfml = ODEInvariance.fStar(ODESystem(sys.ode, True), normalized)._1
    //Points about to leave ODE domain under ODE dynamics
    val bwdfml = ODEInvariance.fStar(ODESystem(oder, True), normalized)._1

    val checkfwd = Imply(And(dom, fwdfml), sys.constraint)
    val prfwd = findCounterExample(checkfwd)

    if (prfwd.nonEmpty)
      return Some("Unable to enter ODE " + sys, prfwd.get)

    val checkbwd = Imply(And(dom, bwdfml), sys.constraint)
    val prbwd = findCounterExample(checkbwd)

    if (prbwd.nonEmpty)
      return Some("Unable to leave ODE " + sys, prbwd.get)

    None
  }

  /** Check that all states can locally evolve under at least one ODE
    *
    * @param odes ODEs in the family
    * @param dom  the expected domain of the overall system (defaults: the entire state space)
    */
  def stateSwitchActive(odes: List[ODESystem], dom: Formula = True): Option[(String, Map[NamedSymbol, Expression])] = {

    val lp = odes.map(
      sys => {
        val (normalized, _) = try {
          SimplifierV3.semiAlgNormalize(sys.constraint)
        } catch {
          case ex: IllegalArgumentException =>
            throw new IllegalArgumentException("Unable to normalize domain to semi-algebraic format: " + sys.constraint, ex)
        }
        ODEInvariance.fStar(ODESystem(sys.ode, True), normalized)._1
      }
    ).reduceRight(Or)

    val check = Imply(dom, lp)
    val pr = findCounterExample(check)

    if (pr.nonEmpty)
      return Some("System cannot evolve forwards", pr.get)

    None
  }

  /** General time dependent switching model
    * Each ODE is indexed 0,...,n-1
    * Each index i can be associated with an (optional) positive time bound t <= T_i for the maximum dwell time
    * Each pair (i,j) can be associated with a positive time tau_{ij} <= t for minimum dwell time before transition
    *
    * @param odes        ODEs in the family with their time bounds
    * @param transitions for each ODE i, an associated list of pairs (j,tau_{ij})
    * @return a hybrid program modeling time-dependent switching between the ODEs
    */
  def timeSwitch(odes: List[(ODESystem, Option[Term])], transitions: List[List[(Int, Term)]],
                 s: Variable = "s_".asVariable, u: Variable = "u_".asVariable, topt: Option[BaseVariable] = None): Program = {

    if (odes.isEmpty)
      throw new IllegalArgumentException("Time-dependent switching requires at least 1 ODE")

    if (odes.length != transitions.length)
      throw new IllegalArgumentException("ODEs and transitions map must have same length")

    val todespre = odes.map(
      (odet) =>
        odet._2 match {
          case None =>
            ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(s), Number(1)), odet._1.ode), odet._1.constraint)
          case Some(tt) =>
            ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(s), Number(1)), odet._1.ode),
              And(odet._1.constraint, LessEqual(s, tt)))
        }
    )

    val todes: List[Program] = topt match {
      case None => todespre
      case Some(t) =>
        todespre.map(ode =>
          ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(t), Number(1)), ode.ode), ode.constraint))
    }

    val resetclk = Assign(s, Number(0))

    //Setting up a choice for each ODE
    // \bigcup_i { ?u=i; ODE_i }
    val plant =
    todes.zipWithIndex.map(todei => Compose(Test(Equal(u, Number(todei._2))), todei._1)).reduceLeft(Choice)

    val ctrl = transitions.zipWithIndex.map(
      it => {
        val (trans, ind) = it
        val transprog =
          trans.map(ij => {
            if (ij._1 < 0 || ij._1 >= odes.length)
              throw new IllegalArgumentException("Unexpected transition to unknown ODE index: " + ij._1)
            if (ij._1 == ind)
              throw new IllegalArgumentException("Self transition not allowed for ODE index: " + ij._1)
            Compose(Test(GreaterEqual(s, ij._2)), Assign(u, Number(ij._1)))
          })
        Compose(
          Test(Equal(u, Number(ind))),
          Choice(
            Compose(transprog.reduceLeft(Choice), resetclk), // Either follow one of the transitions and reset the clock
            Assign(u, Number(ind)) //Or continue running current ODE without switching
          )
        )
      }).reduceLeft(Choice)

    val body = Compose(ctrl, plant)

    // Initialize the system in any ODE
    val init = Compose(resetclk, (0 to transitions.length - 1).map(i => Assign(u, Number(i))).reduceLeft(Choice))

    //    println(ctrl)
    //    println(plant)

    Compose(init, Loop(body))
  }


  /** Standard slow switching model
    * Each ODE is indexed 0,...,n-1
    *
    * @param odes  ODEs in the family
    * @param dwell the (global) minimum dwell time
    * @return a hybrid program modeling slow switching between the ODEs
    */
  def slowSwitch(odes: List[ODESystem], dwell: Term,
                 s: Variable = "s_".asVariable, u: Variable = "u_".asVariable, topt: Option[BaseVariable] = None): Program = {

    val transitions = (0 to odes.length-1).map( i =>
      (0 to odes.length-1).filterNot( j => j == i).map( j =>
        (j, dwell)
      ).toList
    ).toList

    timeSwitch(odes.map(ode => (ode,None)),transitions,s,u,topt)
  }

  /** Stability of the origin for a given hybrid program
    * \forall eps > 0 \exists del > 0
    * \forall x ( ||x|| < del -> [ a ] ||x|| < eps )
    *
    * @param prog    the hybrid program a to specify stability
    * @param varsopt Optional list of variables to quantify and perturb.
    *                By default None will pick non-differential freeVars(a) \cap boundVars(a)
    * @param restr   an optional additional restriction on the initial perturbation
    *
    *                With the additional options, we can write down slightly more nuanced specifications
    *
    *                \forall eps > 0 \exists del > 0
    *                \forall x ( ||x|| < del -> [ a ] ||x|| < eps )
    */
  def stableOrigin(prog: Program, varsopt: Option[List[(Variable,Term)]] = None, restr: Option[Formula] = None): Formula = {

    val bv = StaticSemantics.boundVars(prog).intersect(StaticSemantics.freeVars(prog)).toSet.filterNot(StaticSemantics.isDifferential(_)).map(_.asInstanceOf[Variable])

    val av = StaticSemantics.symbols(prog)

    // Fixed names for now
    val eps = Variable("eps")
    val del = Variable("del")
    if (av.contains(eps) || av.contains(del))
      throw new IllegalArgumentException("Hybrid program must not mention variables eps or del for stability specification")

    val vars: List[Variable] = varsopt match {
      case None => bv.toList
      case Some(vts) => vts.map( vt =>vt._1)
    }

    val normsq = varsopt match {
      case None =>
        vars.map(e => Power(e, Number(2))).reduceLeft(Plus) // ||x||^2
      case Some(vts) =>
        vts.map(ee => Power(Minus(ee._1,ee._2),Number(2))).reduceLeft(Plus)
    }

    val init = restr match {
      case None => Less(normsq, Power(del, Number(2)))
      case Some(f) => And(f, Less(normsq, Power(del, Number(2)))) // Apply a restriction if needed
    }

    val body = Imply(init,
      Box(prog, Less(normsq, Power(eps, Number(2))))
    )
    val qbody = vars.foldRight(body: Formula)((v, f) => Forall(v :: Nil, f))

    Forall(eps :: Nil, Imply(Greater(eps, Number(0)), // \forall eps > 0
      Exists(del :: Nil, And(Greater(del, Number(0)), // \exists del > 0
        qbody
      ))))
  }

  /** Global pre-attractivity of the origin for a given hybrid program
    * \forall eps > 0 \exists del > 0
    * \forall x ( ||x|| < del -> [ a ] ||x|| < eps )
    *
    * @param prog    the hybrid program a to specify stability
    * @param varsopt Optional list of variables to quantify and perturb.
    *                By default None will pick non-differential freeVars(a) \cap boundVars(a)
    * @param restr   an optional additional restriction on the initial perturbation
    *
    *                With the additional options, we can write down slightly more nuanced specifications
    *
    *                \forall eps > 0 \exists del > 0
    *                \forall x ( ||x|| < del -> [ a ] ||x|| < eps )
    */
  def attrOrigin(prog: Program, varsopt: Option[List[(Variable,Term)]] = None, restr: Option[Formula] = None): Formula = {

    val bv = StaticSemantics.boundVars(prog).intersect(StaticSemantics.freeVars(prog)).toSet.filterNot(StaticSemantics.isDifferential(_)).map(_.asInstanceOf[Variable])

    val av = StaticSemantics.symbols(prog)

    // Fixed names for now
    val eps = Variable("eps")
    val del = Variable("del")
    if (av.contains(eps) || av.contains(del))
      throw new IllegalArgumentException("Hybrid program must not mention variables eps or del for stability specification")

    val vars: List[Variable] = varsopt match {
      case None => bv.toList
      case Some(vts) => vts.map( vt =>vt._1)
    }

    val normsq = varsopt match {
      case None =>
        vars.map(e => Power(e, Number(2))).reduceLeft(Plus) // ||x||^2
      case Some(vts) =>
        vts.map(ee => Power(Minus(ee._1,ee._2),Number(2))).reduceLeft(Plus)
    }

    val init = restr match {
      case None => Less(normsq, Power(del, Number(2)))
      case Some(f) => And(f, Less(normsq, Power(del, Number(2)))) // Apply a restriction if needed
    }

    val body = Imply(init,
      Box(prog, Less(normsq, Power(eps, Number(2))))
    )
    val qbody = vars.foldRight(body: Formula)((v, f) => Forall(v :: Nil, f))

    Forall(eps :: Nil, Imply(Greater(eps, Number(0)), // \forall eps > 0
      Exists(del :: Nil, And(Greater(del, Number(0)), // \exists del > 0
        qbody
      ))))
  }

  private lazy val edswap = remember(" f_() < del^2 -> del < eps -> del > 0 -> f_() < eps^2".asFormula, QE, namespace)

  /** Prove stability specification at the given top-level position using the given Lyapunov function V
    * V must satisfy the "basic" properties:
    * V(0) = 0, V > 0 away from the origin
    *
    * Additionally, V must be a "throughout" invariant of the hybrid program
    *
    * @param lyap    the (common) Lyapunov function
    * @param prog    ?
    * @param varsopt ?
    * @param restr   ?
    * @return stability tactic
    */
  def proveStable(lyap: Term, prog: Program, varsopt: Option[List[Variable]] = None, restr: Option[Formula] = None): DependentPositionTactic = anon((pos: Position, seq: Sequent) => {
    if (!(pos.isTopLevel && pos.isSucc))
      throw new IllFormedTacticApplicationException("proveStable: position " + pos + " must point to a top-level succedent position")

    //Note: we might attempt to decipher a stability specification instead
    //    val fml = seq.sub(pos) match {
    //      case Some(f) if f.isInstanceOf[Formula] => f.asInstanceOf[Formula]
    //      case _ => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    //    }

    val bv = StaticSemantics.boundVars(prog).intersect(StaticSemantics.freeVars(prog)).toSet.filterNot(StaticSemantics.isDifferential(_)).map(_.asInstanceOf[Variable])

    val eps = Variable("eps")
    val del = Variable("del")
    val epssq = Power(eps, Number(2))
    val delsq = Power(del, Number(2))

    val w = Variable("w_")

    val vars: List[Variable] = varsopt.getOrElse(bv.toList) //TODO
    val normsq = vars.map(e => Power(e, Number(2))).reduceLeft(Plus) // ||x||^2

    val init = restr match {
      case None => Less(normsq, Power(del, Number(2)))
      case Some(f) => And(f, Less(normsq, Power(del, Number(2)))) // Apply a restriction if needed
    }

    // w serves as an lower bound on V for ||x||=eps
    val epsbound =
      vars.foldRight(Imply(Equal(normsq, epssq), GreaterEqual(lyap, w)): Formula)((v, f) => Forall(v :: Nil, f))
    val epsw = Exists(w :: Nil,
      And(Greater(w, Number(0)),
        epsbound
      ))
    // w serves as an upper bound on V for ||x||<del
    val delw = And(And(Greater(del, Number(0)), Less(del, eps)),
      vars.foldRight(Imply(Less(normsq, delsq), Less(lyap, w)): Formula)((v, f) => Forall(v :: Nil, f))
    )

    val apos = seq.ante.length

    // The relevant tactic for a single ODE
    // Assumes antecedent has the form:
    // assums, \forall x ( |x|=eps -> lyap >= w), lyap < w, |x| < eps
    val odetac =
    dC(Less(lyap, w))(pos) < (
      DifferentialTactics.dCClosure(pos) < (
        hideL(-(apos + 1)) & QE,
        cohideOnlyL(-(apos + 1)) &
          DifferentialTactics.DconstV(pos) &
          DifferentialTactics.diffWeakenG(pos) & implyR(1) &
          andL(-1) & (allL(-1) * vars.length) & QE // can be done by subst
      ),
      hideL(-(apos + 1)) & hideL(-(apos + 2)) & dI('full)(pos)
    )

    // The relevant tactic for a switched system
    val inv = And(Less(lyap, w), Less(normsq, epssq))
    val looptac = loop(inv)(pos) < (
      prop,
      prop,
      implyRi & implyR(pos) & andL('Llast) & chase(pos) &
        SaturateTactic(andR(pos) < (skip, odetac)) & odetac
    )

    val conttac = prog match {
      case ODESystem(_, _) => odetac
      case Loop(_) => looptac
      case _ => skip
    }

    allR(pos) & implyR(pos) &
      cutR(epsw)(pos) < (
        QE,
        implyR(pos) & existsL('Llast) & andL('Llast) &
          existsRmon(delw)(pos) < (
            hideL('Llast) & QE,
            // Get rid of some unused assumptions now
            hideL(-(apos + 1)) & hideL(-(apos + 1)) & andL(-(apos + 2)) & andL(-(apos + 2)) &
              andR(pos) < (
                id,
                (allR(pos) * vars.length) & implyR(pos) &
                  (allL(-(apos + 2)) * vars.length) & implyL(-(apos + 2)) < (
                  id,
                  cutR(Less(normsq, epssq))(pos) < (
                    (implyRi()(AntePos(apos + 2), pos.checkSucc) * 3) & cohideR(pos) & byUS(edswap),
                    (hideL(-(apos + 3)) * 3) & implyR(pos) &
                      conttac
                  )
                )
              )
          )
      )

  })



}