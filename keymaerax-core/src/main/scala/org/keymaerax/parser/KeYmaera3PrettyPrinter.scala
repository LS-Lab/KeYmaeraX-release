/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.core._
import org.keymaerax.infrastruct.PosInExpr
import org.keymaerax.parser.OpSpec.op

import scala.annotation.nowarn

/** Differential Dynamic Logic pretty printer in concrete KeYmaera 3 notation. */
object KeYmaera3PrettyPrinter extends KeYmaeraXPrecedencePrinter {

  /** This default pretty printer. */
  val pp: PrettyPrinter = this

  def printFile(fml: Formula): String = {
    val vars = StaticSemantics.vars(fml).toSet[Variable].filter(_.isInstanceOf[BaseVariable])
    val fns = (StaticSemantics.symbols(fml) -- vars).filter(_.isInstanceOf[Function]).map(_.asInstanceOf[Function])

    @nowarn("msg=match may not be exhaustive")
    def domainDecl(s: Sort): String = s match {
      case Real => "R"
      case Tuple(l, r) => domainDecl(l) + "," + domainDecl(r)
    }

    def fnDomainDecl(fn: Function): String = fn.domain match {
      case Unit => ""
      case d => "(" + domainDecl(d) + ")"
    }

    val fnDecls = fns.map(fn => "R " + fn.prettyString + fnDomainDecl(fn) + ";").mkString("\r\n  ")
    val varsDecls = vars.map("R " + _.prettyString + ";").mkString("\r\n  ")
    val problem = pp(fml)

    s"""
       |\\functions {
       |  $fnDecls
       |}
       |
       |\\programVariables {
       |  $varsDecls
       |}
       |
       |\\problem {
       |  $problem
       |}
    """.stripMargin
  }

  override def apply(expr: Expression): String = stringify(expr)

  /** Pretty-print the operator of a term */
  override protected def ppOp(expr: Expression): String = expr match { case _ => op(expr).opcode }

  /** Pretty-print enclosing parentheses, braces, brackets etc. */
  override protected def wrap(text: String, expr: Expression): String = expr match {
    case _: Box => "\\[" + text + "\\]"
    case _: Diamond => "\\<" + text + "\\>"
    case _: DifferentialProgram => "{" + text + "}"
    case _: ODESystem => "{" + text + "}"
    case _: Program => "(" + text + ")"
    case _: PredicationalOf => throw new IllegalArgumentException("KeYmaera 3 does not support Predicationals")
    case _ => super.wrap(text, expr)
  }

  override protected def pp(q: PosInExpr, term: Term): String = emit(
    q,
    term match {
      case _: DotTerm => throw new IllegalArgumentException("KeYmaera 3 does not support DotTerms")
      case _: Differential => throw new IllegalArgumentException("KeYmaera 3 does not support Differentials")
      case _: UnitFunctional => throw new IllegalArgumentException("KeYmaera 3 does not support UnitFunctionals")
      case FuncOf(f, _) if f.domain == Unit => f.asString
      case _ => super.pp(q, term)
    },
  )

  override protected def pp(q: PosInExpr, formula: Formula): String = emit(
    q,
    formula match {
      case DotFormula => throw new IllegalArgumentException("KeYmaera 3 does not support DotFormulas")
      case PredicationalOf(p, c) => throw new IllegalArgumentException("KeYmaera 3 does not support PredicationalOf")
      case _: UnitPredicational => throw new IllegalArgumentException("KeYmaera 3 does not support UnitPredicationals")
      case f: Quantified => ppOp(formula) + " " + f.vars.map("R " + pp(q, _)).mkString(",") + ". " +
          wrapChild(f, pp(q ++ 0, f.child))
      case _ => super.pp(q, formula)
    },
  )

  override protected def pp(q: PosInExpr, program: Program): String = emit(
    q,
    program match {
      case a: ProgramConst => throw new IllegalArgumentException("KeYmaera 3 does not support ProgramConsts")
      case a: SystemConst => throw new IllegalArgumentException("KeYmaera 3 does not support SystemConsts")
      case _ => super.pp(q, program)
    },
  )

  override protected def ppODE(q: PosInExpr, program: DifferentialProgram): String = emit(
    q,
    program match {
      case a: DifferentialProgramConst =>
        throw new IllegalArgumentException("KeYmaera 3 does not support DifferentialProgramConsts")
      case _ => super.ppODE(q, program)
    },
  )

  override protected def pwrapLeft(t: BinaryComposite, leftPrint: String): String = "(" + leftPrint + ")"
  override protected def pwrapRight(t: BinaryComposite, rightPrint: String): String = "(" + rightPrint + ")"

  override protected def statement(s: String): String = s
}
