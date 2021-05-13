/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, Exists, Forall, Formula, FuncOf, Not, Term, Variable}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.ext.SmtLibReader
import edu.cmu.cs.ls.keymaerax.tools.qe.DefaultSMTConverter

class SmtLibTests extends TacticTestBase {
  /** Prefixes from [[DefaultSMTConverter]]. */
  private val VAR_PREFIX = "_v_"
  private val FUNC_PREFIX = "_f_"
  private val DIFFSYMBOL_PREFIX = "_d_"

  private object round {
    def trip(t: Formula): Formula = { roundTrip(t) shouldBe Not(t); t }
    def roundTrip(t: Formula): Formula = {
      def convertVar(v: Variable): Variable = v match {
        case bv: BaseVariable => bv.copy(name = bv.name.
          replaceAllLiterally(SmtLibReader.USCORE, "_").
          replaceAllLiterally(VAR_PREFIX, ""))
      }

      def convertFml(f: Formula): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
          case Exists(vs, p) => Right(Exists(vs.map(convertVar), convertFml(p)))
          case Forall(vs, p) => Right(Forall(vs.map(convertVar), convertFml(p)))
          case _ => Left(None)
        }
        override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] =  e match {
          case v: BaseVariable => Right(convertVar(v))
          case FuncOf(fn, args) =>
            Right(FuncOf(fn.copy(name = fn.name.
              replaceAllLiterally(SmtLibReader.USCORE, "_").
              replaceAllLiterally(FUNC_PREFIX, "")), args))
          case _ => Left(None)
        }
      }, f).get

      convertFml(SmtLibReader.readFml(DefaultSMTConverter(t))._1)
    }
  }

  "SmtLibReader" should "read simple examples" in {
    round trip "x>=0".asFormula
    round trip "x+1>=0".asFormula
    round trip "\\exists x x>=0".asFormula
    round trip "\\forall x (x<=0|x>=0)".asFormula
  }
}
