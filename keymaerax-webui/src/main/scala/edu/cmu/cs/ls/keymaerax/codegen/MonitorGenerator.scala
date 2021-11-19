/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.btactics.{ModelPlex, SimplifierV3}
import edu.cmu.cs.ls.keymaerax.core.{And, BaseVariable, ComparisonFormula, Diamond, Divide, Equal, Expression, Formula, FuncOf, Greater, GreaterEqual, Less, LessEqual, NamedSymbol, Neg, Not, NotEqual, Nothing, Number, Or, Pair, Plus, Term, Test, True}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.FormulaAugmentor
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, InterpretedSymbols, KeYmaeraXPrettyPrinter}

import scala.annotation.tailrec
import scala.util.Try


/** Base class for monitor generators. Prints expressions with `prettyPrinter`, accesses expressions according to termContainer (e.g., `params.x` or `params->x`). */
abstract class MonitorGenerator(conjunctionsAs: Symbol,
                                defs: Declaration,
                                prettyPrinter: CodePrettyPrinter,
                                termContainer: (Expression, Set[NamedSymbol])=>String) extends CodeGenerator {
  /**
    * Compiles the expression `e` to code as a body of a monitored controller execution function. Forwards `params` to
    * `termContainer` to distinguish between state variables, inputs, parameters etc.
    */
  protected def printMonitor(e: Expression, params: Set[NamedSymbol]): (String, String) = e match {
    case f: Formula if f.isFOL => primitiveExprGenerator(params)(f)
    case f: Formula if !f.isFOL => structuredExprGenerator(params)(f)
    case t: Term => primitiveExprGenerator(params)(t)
    case _ => throw new CodeGenerationException("The input expression: \n" + KeYmaeraXPrettyPrinter(e) + "\nis expected to be a formula or term.")
  }

  private val errorIds = scala.collection.mutable.HashMap[Formula, Int]()

  private def errorId(fml: Formula): Int = {
    if (!errorIds.contains(fml)) errorIds.put(fml, if (errorIds.isEmpty) -1 else errorIds.minBy(_._2)._2-1)
    errorIds(fml)
  }

  private def onlyEqualities(fml: Formula): Boolean = fml match {
    case _: Equal => true
    case And(l, r) => onlyEqualities(l) && onlyEqualities(r)
    case _ => false
  }

  /** Compiles primitive expressions with the appropriate params/curr/pre struct location. */
  private def primitiveExprGenerator(params: Set[NamedSymbol]) = new GenericFormulaTermGenerator(prettyPrinter, termContainer(_, params), defs)

  private def structuredExprGenerator(params: Set[NamedSymbol]) = new GenericFormulaTermGenerator(prettyPrinter, termContainer(_, params), defs) {
    override def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable],
                       modelName: String): (String, String) = expr match {
      case f: Formula if f.isFOL => super.apply(f, stateVars, inputVars, modelName)
      case f: Formula if !f.isFOL => prettyPrinter(compileProgramFormula(f, Number(0)))
      case t: Term => super.apply(t, stateVars, inputVars, modelName)
    }

    //@todo preprocess `f` to collect distance measure `dist` by proof instead of here:
    // transform <?s=t><?x<=y><?a<=b>true into <?s=t><?x<=y><?a<=b>min(x-y,a-b)>=0
    private def compileProgramFormula(f: Formula, dist: Term): CProgram = f match {
      case Or(Diamond(Test(p), ifP), Diamond(Test(Not(q)), elseP)) if p==q =>
        val ifDist = if (onlyEqualities(p)) dist else ModelPlex.toMetric(p) match {
          //@todo toMetric returns negated to what we assume here
          case c: ComparisonFormula => Plus(dist, Neg(c.left))
        }
        val elseDist = if (onlyEqualities(p)) dist else ModelPlex.toMetric(Not(q)) match {
          //@todo toMetric returns negated to what we assume here
          case c: ComparisonFormula => Plus(dist, Neg(c.left))
        }
        CIfThenElse(compileFormula(p), compileProgramFormula(ifP, ifDist), compileProgramFormula(elseP, elseDist))
      case Or(l, r) => COrProgram(compileProgramFormula(l, Number(0)), compileProgramFormula(r, Number(0)))
      case And(l, r) => CAndProgram(compileProgramFormula(l, Number(0)), compileProgramFormula(r, Number(0)))
      case True => CReturn(compileTerm(dist))
      case Diamond(Test(p), q) =>
        val (pMetric: Term, pSatDist) = conjunctionsAs match {
          case 'min => printAndMin(p, dist)
          case 'resist => printAndParallelResistors(p, dist)
        }
        //@note offset error distance from -1 since weak inequalities may otherwise result in safe distance 0
        val errorDist = CPlus(CNumber(-1), compileTerm(pMetric))
        CIfThenElse(compileFormula(p), compileProgramFormula(q, pSatDist), CError(errorId(p), errorDist, p.prettyString))
    }
  }

  /** Combines conjunction of distance `dist` and metric of `p` with min. */
  @tailrec
  private def printAndMin(p: Formula, dist: Term): (Term, Term) = Try(ModelPlex.toMetric(p)).toOption match {
    //@note when all nested ifs are satisfied, dist>=0; otherwise dist<=0. Resulting first term has same property.
    case Some(c: ComparisonFormula) =>
      assert(c.right == Number(0))
      // we want safety margin>=0 when formula is true
      val margin: Term = c match {
        //@note incorrect translation of greater/less prevented with outside if(x>y) margin else error
        case _: GreaterEqual | _: Greater => c.left
        case _: LessEqual | _: Less => Neg(c.left)
        case _: Equal => Neg(FuncOf(InterpretedSymbols.absF, c.left))
        case _: NotEqual => FuncOf(InterpretedSymbols.absF, c.left)
      }
      val simpMargin = SimplifierV3.termSimp(margin, scala.collection.immutable.HashSet.empty, SimplifierV3.defaultTaxs)._1
      val errorMargin = simpMargin
      val combinedMargin = FuncOf(InterpretedSymbols.minF, Pair(dist, simpMargin))
      (errorMargin, if (onlyEqualities(p)) dist else combinedMargin)
    case _ =>
      val psubst = defs.exhaustiveSubst(p)
      if (psubst != p) printAndMin(psubst, dist)
      //@note unable to translate to distance, propagate invalid distance upwards
      else (Nothing, Nothing)
  }

  /** Combines conjunction of distance `dist` and metric of `p` in analogy to total resistance of parallel resistors 1/(1/dist + 1/metric(p))) */
  @tailrec
  private def printAndParallelResistors(p: Formula, dist: Term): (Term, Term) = Try(ModelPlex.toMetric(p)).toOption match {
    //@note when all nested ifs are satisfied, dist>=0; otherwise dist<=0. Resulting first term has same property.
    // Encode And as 1/(1/x+1/y) (instead of min) has the advantage that changes in each conjunct
    // are reflected in the combined safety distance
    case Some(c: ComparisonFormula) =>
      assert(c.right == Number(0))
      // we want safety margin>=0 when formula is true
      val margin: Term = c match {
        //@note incorrect translation of greater/less prevented with outside if(x>y) margin else error
        case _: GreaterEqual | _: Greater => c.left
        case _: LessEqual | _: Less => Neg(c.left)
        case _: Equal => Neg(FuncOf(InterpretedSymbols.absF, c.left))
        case _: NotEqual => FuncOf(InterpretedSymbols.absF, c.left)
      }
      val simpMargin = SimplifierV3.termSimp(margin, scala.collection.immutable.HashSet.empty, SimplifierV3.defaultTaxs)._1
      val (errorMargin, combinedMargin) = dist match {
        case Nothing => (Nothing, Nothing)
        case Number(n) if n == 0 => (simpMargin, simpMargin)
        case Divide(Number(n), Plus(l: Divide, r)) if n == 1 =>
          //@note parallel composition of successive tests (n-ary conjunction)
          (simpMargin, Divide(Number(1), Plus(l, Plus(r, Divide(Number(1), simpMargin)))))
        case _ =>
          //@todo other non-obvious divisions by zero
          (simpMargin, Divide(Number(1), Plus(Divide(Number(1), dist), Divide(Number(1), simpMargin))))
      }
      (errorMargin, if (onlyEqualities(p)) dist else combinedMargin)
    case _ =>
      val psubst = defs.exhaustiveSubst(p)
      if (psubst != p) printAndParallelResistors(psubst, dist)
      //@note unable to translate to distance, propagate invalid distance upwards
      else (Nothing, Nothing)
  }
}

/** Generates a monitor expression without surrounding function head, comments. */
class SimpleMonitorGenerator(conjunctionsAs: Symbol, defs: Declaration,
                             prettyPrinter: CodePrettyPrinter,
                             termContainer: (Expression, Set[NamedSymbol])=>String)
  extends MonitorGenerator(conjunctionsAs, defs, prettyPrinter, termContainer) {
  /** @inheritdoc */
  override def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable], modelName: String): (String, String) = {
    printMonitor(expr, CodeGenerator.getParameters(defs.exhaustiveSubst(expr), stateVars))
  }
}