/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.tools

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal
import ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion._
import edu.cmu.cs.ls.keymaerax.tools.SimulationTool.{SimRun, SimState, Simulation}

import scala.collection.immutable

object ToolConversions {

  def flattenConjunctions(f: Formula): List[Formula] = {
    var result: List[Formula] = Nil
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
        case And(l, r) => result = result ++ flattenConjunctions(l) ++ flattenConjunctions(r); Left(Some(ExpressionTraversal.stop))
        case a => result = result :+ a; Left(Some(ExpressionTraversal.stop))
      }
    }, f)
    result
  }
}

class UncheckedM2KConverter extends MathematicaToKeYmaera {
  //@note unchecked, because ambiguous And==&& vs. And==Rules conversion
  override def k2m = null
  override def apply(e: MExpr): KExpr = convert(e)

  /** Extends default converter with rule and rule list handling */
  override def convert(e: MExpr): KExpr = {
    if (MathematicaToKeYmaera.hasHead(e, MathematicaSymbols.RULE)) convertRule(e)
    else if (e.listQ() && e.args().forall(r => r.listQ() && r.args().forall(
      MathematicaToKeYmaera.hasHead(_, MathematicaSymbols.RULE)))) convertRuleList(e)
    else super.convert(e)
  }

  /** Converts rules and rule lists, not to be used in QE! */
  def convertRule(e: MExpr): Formula = {
    Equal(convert(e.args()(0)).asInstanceOf[Term], convert(e.args()(1)).asInstanceOf[Term])
  }

  def convertRuleList(e: MExpr): Formula = {
    val convertedRules = e.args().map(_.args().map(r => convertRule(r)).reduceLeft(And))
    if (convertedRules.isEmpty) False
    else convertedRules.reduceLeft(Or)
  }
}

class UncheckedK2MConverter extends KeYmaeraToMathematica {
  //@note unchecked, because ambiguous And==&& vs. And==Rule in converse conversion
  override def m2k = null
  override def apply(e: KExpr): MExpr = convert(e)
}

object CEXK2MConverter extends UncheckedK2MConverter {
  val CONST_FN_PREFIX = "fn$"

  override def convert(e: KExpr): MExpr = e match {
    case Function(name, index, Unit, _) => MathematicaNameConversion.toMathematica(Variable(CONST_FN_PREFIX + name, index))
    case _ => super.convert(e)
  }

  override protected def convertTerm(t: Term): MExpr = t match {
    //@note no back conversion -> no need to distinguish Differential from DifferentialSymbol
    case Differential(c) =>
      new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), Array[MExpr](convert(c)))
    case DifferentialSymbol(c) =>
      new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), Array[MExpr](convert(c)))
    case FuncOf(Function(name, index, Unit, _), Nothing) => MathematicaNameConversion.toMathematica(Variable(CONST_FN_PREFIX + name, index))
    case _ => super.convertTerm(t)
  }
}

object CEXM2KConverter extends UncheckedM2KConverter {
  override def k2m = null
  override def apply(e: MExpr): KExpr = convert(e)

  override protected def convertAtomicTerm(e: MExpr): KExpr = {
    MathematicaNameConversion.toKeYmaera(e) match {
      case Variable(name, index, sort) if name.startsWith(CEXK2MConverter.CONST_FN_PREFIX) =>
        FuncOf(Function(name.replace(CEXK2MConverter.CONST_FN_PREFIX, ""), index, Unit, sort), Nothing)
      case _ => super.convertAtomicTerm(e)
    }
  }
}

/**
 * Mathematica counter example implementation.
  *
  * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class MathematicaCEXTool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[KExpr](link, CEXK2MConverter, CEXM2KConverter) with CounterExampleTool {

  private val TIMEOUT = 10

  def findCounterExample(fml: Formula): Option[Map[NamedSymbol, Term]] = {
    val input = new MExpr(new MExpr(Expr.SYMBOL,  "FindInstance"),
      Array(k2m.convert(Not(fml)),
        new MExpr(
          MathematicaSymbols.LIST,
          StaticSemantics.symbols(fml).toList.sorted.map(s => k2m.convert(s)).toArray),
        new MExpr(Expr.SYMBOL, "Reals")))
    val inputWithTO = new MExpr(new MExpr(Expr.SYMBOL,  "TimeConstrained"), Array(input, k2m(Number(TIMEOUT))))

    run(inputWithTO) match {
      case (_, cex: Formula) => cex match {
        case False =>
          if (DEBUG) println("No counterexample, Mathematica returned: " + cex.prettyString)
          None
        case _ =>
          if (DEBUG) println("Counterexample " + cex.prettyString)
          Some(ToolConversions.flattenConjunctions(cex).map({
            case Equal(name: NamedSymbol, value) => name -> value
            case Equal(FuncOf(fn, _), value) => fn -> value
          }).toMap)
      }
      case result =>
        if (DEBUG) println("No counterexample, Mathematica returned: " + result)
        None
    }
  }
}

/**
  * A link to Mathematica using the JLink interface.
  *
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
class MathematicaODETool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[KExpr](link, new UncheckedK2MConverter, new UncheckedM2KConverter) with DiffSolutionTool with DerivativeTool {

  def diffSol(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Variable]): Option[Formula] =
    diffSol(diffArg, iv, toDiffSys(diffSys, diffArg):_*)

  /**
    * Converts a system of differential equations given as DifferentialProgram into list of x'=theta
    *
    * @param diffSys The system of differential equations
    * @param diffArg The name of the differential argument (dx/d diffArg = theta).
    * @return The differential equation system in list form.
    */
  private def toDiffSys(diffSys: DifferentialProgram, diffArg: Variable): List[(Variable, Term)] = {
    var result = List[(Variable, Term)]()
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
        case AtomicODE(DifferentialSymbol(x), theta) if x != diffArg => result = result :+ (x, theta); Left(None)
        case AtomicODE(DifferentialSymbol(x), theta) if x == diffArg => Left(None)
        case ODESystem(_, _) => Left(None)
        case DifferentialProduct(_, _) => Left(None)
      }
    }, diffSys)
    result
  }

  /**
    * Computes the symbolic solution of a system of differential equations.
    *
    * @param diffArg The differential argument, i.e., d f(diffArg) / d diffArg.
    * @param diffSys The system of differential equations of the form x' = theta.
    * @return The solution if found; None otherwise
    */
  private def diffSol(diffArg: Variable, iv: Map[Variable, Variable], diffSys: (Variable, Term)*): Option[Formula] = {
    val primedVars = diffSys.map(_._1)
    val functionalizedTerms = diffSys.map{ case (x, theta) => ( x, functionalizeVars(theta, diffArg, primedVars:_*)) }
    val mathTerms = functionalizedTerms.map{case (x, theta) =>
      val diffSymbol = new MExpr(new MExpr(MathematicaSymbols.DERIVATIVE, Array[MExpr](new MExpr(1))), Array[MExpr](k2m(x)))
      (new MExpr(diffSymbol, Array[MExpr](k2m(diffArg))), k2m(theta))}
    val convertedDiffSys = mathTerms.map{case (x, theta) =>
      new MExpr(MathematicaSymbols.EQUALS, Array[MExpr](x, theta))}

    val functions = diffSys.map(t => k2m(functionalizeVars(t._1, diffArg)))

    val initialValues = diffSys.map(t => k2m(
      Equal(functionalizeVars(t._1, Number(BigDecimal(0)), primedVars:_*), iv(t._1))))

    val input = new MExpr(new MExpr(Expr.SYMBOL, "DSolve"),
      Array[MExpr](
        new MExpr(Expr.SYM_LIST, (convertedDiffSys ++ initialValues).toArray),
        new MExpr(Expr.SYM_LIST, functions.toArray),
        k2m(diffArg)))
    val (_, result) = run(input)
    result match {
      case f: Formula => Some(defunctionalize(f, diffArg, primedVars.map(_.name):_*))
      case _ => None
    }
  }

  /**
    * Replaces all occurrences of variables vars in the specified term t with functions of argument arg.
    *
    * @param t The term.
    * @param arg The function argument.
    * @param vars The variables to functionalize.
    * @return The term with variables replaced by functions.
    */
  private def functionalizeVars(t: Term, arg: Term, vars: Variable*) = ExpressionTraversal.traverse(
    new ExpressionTraversalFunction {
      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case v@Variable(name, idx, sort) if vars.isEmpty || vars.contains(v) =>
          Right(FuncOf(Function(name, idx, arg.sort, sort), arg))
        case _ => Left(None)
      }
    }, t) match {
    case Some(resultTerm) => resultTerm
    case None => throw new IllegalArgumentException("Unable to functionalize " + t)
  }

  /**
    * Replaces all functions with argument arg in formula f with a variable of the same name.
    *
    * @param f The formula.
    * @param arg The function argument.
    * @return The term with functions replaced by variables.
    */
  private def defunctionalize(f: Formula, arg: Term, fnNames: String*) = ExpressionTraversal.traverse(
    new ExpressionTraversalFunction {
      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case FuncOf(Function(name, idx, _, range), fnArg) if arg == fnArg
          && (fnNames.isEmpty || fnNames.contains(name)) => Right(Variable(name, idx, range))
        case _ => Left(None)
      }
    }, f) match {
    case Some(resultF) => resultF
    case None => throw new IllegalArgumentException("Unable to defunctionalize " + f)
  }

  def deriveBy(term: Term, v: Variable): Term = {
    val mathTerm = k2m(term)
    val mathVar = k2m(v)
    val input = new MExpr(MathematicaSymbols.D, Array[MExpr](mathTerm, mathVar))
    val (_, result) = run(input)
    result match {
      case t: Term => t
    }
  }
}

object SimulationM2KConverter extends BaseM2KConverter[Simulation] {

  //@note unchecked, because in back-translation we don't know whether end-of-world 'false' was present in original or not
  def k2m: K2MConverter[Simulation] = null
  override def apply(e: MExpr): Simulation = convert(e)

  private val m2k: M2KConverter[KExpr] = new UncheckedM2KConverter

  override def convert(e: MExpr): Simulation = {
    if (e.listQ() && e.args.forall(_.listQ())) {
      val states: Array[Array[KExpr]] = e.args().map(_.args().map(m2k))
      states.map(state => {
        val endOfWorld = if (state.contains(False)) state.indexOf(False) else state.length
        state.slice(0, endOfWorld).map({
          case fml: Formula => ToolConversions.flattenConjunctions(fml).map({
            case Equal(name: NamedSymbol, value: Number) => name -> value
            case Equal(FuncOf(fn, _), value: Number) => fn -> value
            case s => throw new IllegalArgumentException("Expected state description Equal(...), but got " + s)
          }).toMap
          case s => throw new IllegalArgumentException("Expected state formula, but got " + s)
        }).toList}).toList
    } else throw new IllegalArgumentException("Expected list of simulation states, but got " + e)
  }
}

object SimulationK2MConverter extends BaseK2MConverter[Simulation] {

  //@note unchecked, because don't know whether end-of-world 'false' was present in original or not
  def m2k = null
  override def apply(e: Simulation): MExpr = convert(e)

  private val k2m: K2MConverter[KExpr] = new UncheckedK2MConverter

  override def convert(e: Simulation): MExpr = {
    new MExpr(MathematicaSymbols.LIST,
      e.map(r => new MExpr(MathematicaSymbols.LIST,
        r.map(s => k2m(s.map{ case (n: Term, v) => Equal(n, v) }.reduceLeft(And))).toArray)).toArray)
  }
}

/**
  * A link to Mathematica using the JLink interface.
  *
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
class MathematicaSimulationTool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[Simulation](link, SimulationK2MConverter, SimulationM2KConverter) with SimulationTool {
  private val basek2m = new UncheckedK2MConverter

  def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation = {
    // init[n_] := Map[List[#]&, FindInstance[a>=..., {a, ...}, Reals, n]] as pure function
    val init = new MExpr(new MExpr(Expr.SYMBOL, "SetDelayed"), Array(
      new MExpr(Expr.SYMBOL, "init"),
      new MExpr(new MExpr(Expr.SYMBOL, "Function"), Array(
        new MExpr(new MExpr(Expr.SYMBOL, "Map"), Array(
          new MExpr(new MExpr(Expr.SYMBOL, "Function"), Array(new MExpr(MathematicaSymbols.LIST, Array(new MExpr(Expr.SYMBOL, "#"))))),
          new MExpr(new MExpr(Expr.SYMBOL,  "FindInstance"),
            Array(basek2m(initial),
              new MExpr(
                MathematicaSymbols.LIST,
                StaticSemantics.symbols(initial).toList.sorted.map(basek2m).toArray),
              new MExpr(Expr.SYMBOL, "Reals"),
              new MExpr(Expr.SYMBOL, "#")))))))))
    // step[pre_] := Module[{apre=a/.pre, ...}, FindInstance[apre>=..., {a, ...}, Reals]] as pure function
    val (stepPreVars, stepPostVars) = StaticSemantics.symbols(stateRelation).partition(_.name.startsWith("pre"))
    val pre2post = stepPostVars.filter(_.name != "t_").map(v => Variable("pre" + v.name, v.index, v.sort) -> v).toMap[NamedSymbol, NamedSymbol]
    val stepModuleInit = stepPreVars.toList.sorted.map(s =>
      new MExpr(new MExpr(Expr.SYMBOL, "Set"), Array(
        basek2m(s),
        new MExpr(new MExpr(Expr.SYMBOL, "ReplaceAll"), Array(
          basek2m(pre2post.getOrElse(s, throw new IllegalArgumentException("No post variable for " + s.prettyString))),
          new MExpr(Expr.SYMBOL, "#")))))).toArray
    val step = new MExpr(new MExpr(Expr.SYMBOL, "SetDelayed"), Array(
      new MExpr(Expr.SYMBOL, "step"),
      new MExpr(new MExpr(Expr.SYMBOL, "Function"),
        Array(new MExpr(new MExpr(Expr.SYMBOL, "Module"),
          Array(new MExpr(MathematicaSymbols.LIST, stepModuleInit),
            new MExpr(new MExpr(Expr.SYMBOL,  "FindInstance"),
              Array(basek2m(stateRelation),
                new MExpr(
                  MathematicaSymbols.LIST,
                  stepPostVars.toList.sorted.map(basek2m).toArray),
                new MExpr(Expr.SYMBOL, "Reals")))))))))
    // Map[N[NestList[step,#,steps]]&, init[n]]
    val exec = new MExpr(new MExpr(Expr.SYMBOL, "Map"), Array(
      new MExpr(new MExpr(Expr.SYMBOL, "Function"),
        Array(new MExpr(new MExpr(Expr.SYMBOL, "N"), Array(new MExpr(new MExpr(Expr.SYMBOL, "NestList"),
          Array(new MExpr(Expr.SYMBOL, "step"), new MExpr(Expr.SYMBOL, "#"), new MExpr(steps))))))),
      new MExpr(new MExpr(Expr.SYMBOL, "Apply"), Array(new MExpr(Expr.SYMBOL, "init"),
        new MExpr(MathematicaSymbols.LIST, Array(new MExpr(n)))))))
    // initial;step;simulate
    val simulate = new MExpr(new MExpr(Expr.SYMBOL, "CompoundExpression"), Array(init, step, exec))

    run(simulate)._2
  }

  def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun = ???
}