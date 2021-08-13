package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
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

  /** Basic state dependent switching models
    *
    * @param odes ODEs in the family
    * @param topt an optional time variable to track time (if included, all ODEs are augmented with t'=1)
    * @return a hybrid program modeling state-dependent (or arbitrary) switching between the ODEs
    */
  def stateSwitch(odes : List[ODESystem], topt: Option[BaseVariable] = None ): Program = {

    if(odes.isEmpty)
      throw new IllegalArgumentException("State-dependent switching requires at least 1 ODE")

    val todes : List[Program] = topt match {
      case None => odes
      case Some(t) =>
        if(odes.exists(ode => StaticSemantics.vars(ode).contains(t)))
          throw new IllegalArgumentException("Time variable " + t +" must be fresh in ODE family " + odes)

        odes.map( ode =>
          ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(t),Number(1)),ode.ode),ode.constraint))
    }

    // arbitrary switching choice is modeled by dL's ++
    val body = todes.reduceLeft(Choice)

    // repeated switching is modeled by dL's *
    Loop(body)
  }

  /** Check that ODE's domain includes points that are about to locally exit or enter it under the dynamics of the ODE
    * @note for closed domains, this is automatically true
    * @note returns an option with string and counterexample if it manages to find one
    * @param sys the ODE under consideration
    * @param dom the "global" domain of points to be considered
    */
  def odeActive(sys : ODESystem, dom : Formula = True) : Option[(String, Map[NamedSymbol, Expression])] = {

    val odels = DifferentialProduct.listify(sys.ode).map {
      case AtomicODE(x,e) => (x,e)
      case _ => throw new IllegalArgumentException("ODE sanity checks can only be used on concrete ODEs.")
    }
    val oder = odels.map( xe => AtomicODE(xe._1,Neg(xe._2))).reduceRight(DifferentialProduct.apply)

    val (normalized,_) = try {
      SimplifierV3.semiAlgNormalize(sys.constraint)
    } catch {
      case ex: IllegalArgumentException =>
        throw new IllegalArgumentException("Unable to normalize domain to semi-algebraic format: "+ sys.constraint, ex)
    }

    //Points about to enter ODE domain under ODE dynamics
    val fwdfml = ODEInvariance.fStar(ODESystem(sys.ode, True), normalized)._1
    //Points about to leave ODE domain under ODE dynamics
    val bwdfml = ODEInvariance.fStar(ODESystem(oder, True), normalized)._1

    val checkfwd = Imply(And(dom,fwdfml),sys.constraint)
    val prfwd = findCounterExample(checkfwd)

    if(prfwd.nonEmpty)
      return Some("Unable to enter ODE "+sys,prfwd.get)

    val checkbwd = Imply(And(dom,bwdfml),sys.constraint)
    val prbwd = findCounterExample(checkbwd)

    if(prbwd.nonEmpty)
      return Some("Unable to leave ODE "+sys,prbwd.get)

    None
  }

  /** Check that all states can locally evolve under at least one ODE
    *
    * @param odes ODEs in the family
    * @param dom the expected domain of the overall system (defaults: the entire state space)
    */
  def stateSwitchActive(odes : List[ODESystem], dom : Formula = True) : Option[(String, Map[NamedSymbol, Expression])] = {

    val lp = odes.map(
      sys => {
        val (normalized,_) = try {
          SimplifierV3.semiAlgNormalize(sys.constraint)
        } catch {
          case ex: IllegalArgumentException =>
            throw new IllegalArgumentException("Unable to normalize domain to semi-algebraic format: "+ sys.constraint, ex)
        }
        ODEInvariance.fStar(ODESystem(sys.ode, True), normalized)._1
      }
    ).reduceRight(Or)

    val check = Imply(dom,lp)
    val pr = findCounterExample(check)

    if(pr.nonEmpty)
      return Some("System cannot evolve forwards",pr.get)

    None
  }

}
