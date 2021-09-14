package edu.cmu.cs.ls.keymaerax.tools.qe

import edu.cmu.cs.ls.keymaerax.core.{AtomicODE, BaseVariable, DifferentialProduct, DifferentialProgram, DifferentialSymbol, Equal, FuncOf, Function, Number, ODESystem, Program, Term, Variable}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.tools.ConversionException
import edu.cmu.cs.ls.keymaerax.tools.ext.ExtMathematicaOpSpec
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion.MExpr

import scala.collection.immutable.{List, Map}
import scala.math.BigDecimal

case class DifferentialProgramToMathematica(k2m: K2MConverter[MathematicaConversion.KExpr]) {
  /**
    * Converts a DifferentialProgram to a Mathematica expression.
    * This code is largely copy/pasted from MathematicaTools.MathematicalODESolvertool, so that we can KeYmaera
    * translations of ODEs in other contexts.
    * @return a 4-tuple containing:
    *         a list of MExprs specifying the ODEs,
    *         a list of MExprs specifying symbolic initial conditions,
    *         a list of MExprs specifying functions (IDK what this is actually -- check the dsolve code and Wolfram documentaiton to figure out)
    *         the variable used as the time variable (diffArg, as passed in initially)
    * @author Nathan Fulton
    */
  def apply(dp: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Variable]): (List[MExpr], List[MExpr], List[MExpr], Variable) = {
    /**
      * @note copied from MathematicaTools.MathematicalODESolvertool.
      */
    def toDiffSys(diffSys: DifferentialProgram, diffArg: Variable): List[(Variable, Term)] = {
      var result = List[(Variable, Term)]()
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
          case AtomicODE(DifferentialSymbol(x), theta) if x != diffArg => result = result :+ (x, theta); Left(None)
          case AtomicODE(DifferentialSymbol(x), _) if x == diffArg => Left(None)
          case ODESystem(_, _) => Left(None)
          case DifferentialProduct(_, _) => Left(None)
        }
      }, diffSys)
      result
    }

    /** @note coped from dsolve tool. */
    def functionalizeVars(t: Term, arg: Term, vars: Variable*) = ExpressionTraversal.traverse(
      new ExpressionTraversalFunction {
        override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          case v@BaseVariable(name, idx, sort) if vars.isEmpty || vars.contains(v) =>
            Right(FuncOf(Function(name, idx, arg.sort, sort), arg))
          case _ => Left(None)
        }
      }, t) match {
      case Some(resultTerm) => resultTerm
      case None => throw ConversionException("Unable to functionalize " + t)
    }

    val diffSys = toDiffSys(dp, diffArg)

    val primedVars = diffSys.map(_._1)
    val functionalizedTerms = diffSys.map{ case (x, theta) => ( x, functionalizeVars(theta, diffArg, primedVars:_*)) }
    val mathTerms = functionalizedTerms.map({case (x, theta) =>
      (ExtMathematicaOpSpec.dx(ExtMathematicaOpSpec.primed(k2m(x)))(k2m(diffArg)), k2m(theta))})
    val convertedDiffSys = mathTerms.map({case (x, theta) => MathematicaOpSpec.equal(x, theta)})

    val functions = diffSys.map(t => k2m(functionalizeVars(t._1, diffArg)))

    //@todo allows for partial initial conditions, but this will probably cause issues if IVs are used.
    val initialValues = diffSys
      .map(t =>
        iv.get(t._1) match {
          case Some(definedInitialValue) =>
            Some(
              Equal(functionalizeVars(t._1, Number(BigDecimal(0)), primedVars:_*), definedInitialValue)
            )
          case None => None //@todo perhaps add an error here?
        }
      )
      .filterNot(x => x.isEmpty)
      .map(x => k2m(x.get))

    (convertedDiffSys, initialValues, functions, diffArg)
  }
}
