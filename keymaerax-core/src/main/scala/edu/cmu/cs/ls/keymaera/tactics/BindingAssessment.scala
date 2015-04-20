package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._

import scala.collection.immutable.Set

/**
 * Created by aplatzer on 4/13/15.
 */
@deprecated("Use StaticSemantics instead")
object BindingAssessment {
  /**
   * Categorizes the names of formula f into free variables FV and bound variables BV.
   * @param f The formula to categorize.
   * @return The names in f categorized into free and bound names.
   */
  @deprecated("Use StaticSemantics(f) instead")
  def catVars(f: Formula) = StaticSemantics(f)

  /**
   * The set of all (may) free variables whose value t depends on (syntactically).
   */
  @deprecated("Use StaticSemantics(t) or StaticSemantics.freeVars(t) instead")
  def freeVariables(t: Term): SetLattice[NamedSymbol] = StaticSemantics(t)

  @deprecated("Use StaticSemantics(p) instead")
  def catVars(p: Program) = StaticSemantics(p)

  def primedVariables(ode: DifferentialProgram): Set[NamedSymbol] = ode match {
    case DifferentialProduct(a, b) => primedVariables(a) ++ primedVariables(b)
    case ODESystem(child, _) => primedVariables(child)
    case AtomicODE(DifferentialSymbol(x), _) => Set(x)
    case _: DifferentialProgramConst => Set.empty
  }

  @deprecated("Use StaticSemantics.symbols(t) instead.")
  def allNames(t: Term): Set[NamedSymbol] = StaticSemantics.symbols(t)

  @deprecated("Use StaticSemantics.symbols(f) instead.")
  def allNames(f: Formula): Set[NamedSymbol] = StaticSemantics.symbols(f)

  @deprecated("Use StaticSemantics.symbols(p) instead.")
  def allNames(p: Program): Set[NamedSymbol] = StaticSemantics.symbols(p)


  @deprecated("Move to Skolemize")
  def allNamesExceptAt(s: Sequent, p: Position) = {
    require(p.inExpr == HereP, "Can only skolemize top level formulas")
    val fs = if (p.isAnte) s.ante.slice(0, p.index) ++ s.ante.slice(p.index + 1, s.ante.length) ++ s.succ
             else s.ante ++ s.succ.slice(0, p.index) ++ s.succ.slice(p.index + 1, s.ante.length)
    fs.flatMap(BindingAssessment.allNames).toSet
  }
}
