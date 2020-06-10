/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic pretty printer in concrete KeYmaera X notation.
  *
  * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @note Code Review 2016-08-02
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.parser.OpSpec.op
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr.HereP

import scala.collection.immutable._
import org.typelevel.paiges._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.mutable.ListBuffer

/**
 * Default KeYmaera X Pretty Printer formats differential dynamic logic expressions
  *
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrecedencePrinter]]
 */
object KeYmaeraXPrettyPrinter extends KeYmaeraXPrecedencePrinter {
  /** This default pretty printer. */
  val pp: KeYmaeraXPrettyPrinter.type = this
}

/**
  * KeYmaera X Pretty Printer without contract checking
  *
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrecedencePrinter]]
  */
object KeYmaeraXNoContractPrettyPrinter extends KeYmaeraXPrecedencePrinter {
  /** This default pretty printer without contract checking. */
  val pp: KeYmaeraXNoContractPrettyPrinter.type = this

  override def apply(expr: Expression): String = stringify(expr)
}

/**
  * Common base functionality for KeYmaera X Pretty Printers.
  */
trait BasePrettyPrinter extends PrettyPrinter {

  /** Pretty-print term to a string */
  def apply(expr: Expression): String = stringify(expr) ensures(
    r => expr.kind == FunctionKind || reparse(expr, r) == expr,
    "Expect parse of print to be identity." +
      //@todo reconcile first and last line of contract message
      "\nExpression: " + FullPrettyPrinter.stringify(expr) + "\t@ " + expr.getClass.getSimpleName +
      "\nPrinted:    " + stringify(expr) +
      "\nReparsed:   " + stringify(reparse(expr, stringify(expr))) + "\t@ " + reparse(expr, stringify(expr)).getClass.getSimpleName +
      "\nExpression: " + FullPrettyPrinter.stringify(reparse(expr, stringify(expr))) + "\t@ " + reparse(expr, stringify(expr)).getClass.getSimpleName +
      "\nExpected:   " + FullPrettyPrinter.stringify(expr) + "\t@ " + expr.getClass.getSimpleName
    )

  /** Pretty-print sequent to a string */
  def apply(seq: Sequent): String =
    (1 to seq.ante.length).map(i => -i + ":  " + apply(seq.ante(i - 1)) + "\t" + seq.ante(i - 1).getClass.getSimpleName).mkString("\n") +
      "\n  ==>  \n" +
      (1 to seq.succ.length).map(i => +i + ":  " + apply(seq.succ(i - 1)) + "\t" + seq.succ(i - 1).getClass.getSimpleName).mkString("\n")

  /** Pretty-print sequent to a string but without contract checking! */
  private[keymaerax] def stringify(seq: Sequent): String =
    (1 to seq.ante.length).map(i => -i + ":  " + stringify(seq.ante(i - 1)) + "\t" + seq.ante(i - 1).getClass.getSimpleName).mkString("\n") +
      "\n  ==>  \n" +
      (1 to seq.succ.length).map(i => +i + ":  " + stringify(seq.succ(i - 1)) + "\t" + seq.succ(i - 1).getClass.getSimpleName).mkString("\n")

  /** Reparse the string print as the same kind as expr has */
  private def reparse(expr: Expression, print: String): Expression = expr.kind match {
    case TermKind => parser.termParser(print)
    case FormulaKind => parser.formulaParser(print)
    case ProgramKind => parser.programParser(print)
    case DifferentialProgramKind => parser.differentialProgramParser(print)
    case FunctionKind => throw new AssertionError("No completed expressions of FunctionKind can be constructed")
    case ExpressionKind => throw new AssertionError("No expressions of ExpressionKind can be constructed")
  }

  /** Pretty-print term to a string but without contract checking! */
  private[keymaerax] def stringify(expr: Expression): String
}

/**
  * Fully-parenthesized pretty printer in full form with full parentheses.
  *
  * @example
  * Fully parenthesized strings are obtained using the [[edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter]] printer:
  * {{{
  * val pp = FullPrettyPrinter
  * // "x < -(y)"
  * val fml0 = Less(Variable("x"),Neg(Variable("y")))
  * val fml0str = pp(fml0)
  * // "true -> ([x:=1;](x>=0))"
  * val fml1 = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
  * val fml1str = pp(fml1)
  * }}}
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrinter.fullPrinter]]
  */
object FullPrettyPrinter extends BasePrettyPrinter {

  import OpSpec.op
  import OpSpec.statementSemicolon

  val parser: KeYmaeraXParser.type = KeYmaeraXParser
  val fullPrinter: (Expression => String) = this


  /** Pretty-print term to a string but without contract checking! */
  private[keymaerax] def stringify(expr: Expression): String = expr match {
    case t: Term    => pp(t)
    case f: Formula => pp(f)
    case p: Program => pp(p)
    case f: Function => f.asString
  }

  /**@note The extra space disambiguates x<-7 as in x < (-7) from x REVIMPLY 7 as well as x<-(x^2) from x REVIMPLY ... */
  private val LEXSPACE: String = " "

  private def pp(term: Term): String = term match {
    case Nothing       => op(term).opcode
    //@note DotTerm does not have an OpSpec img because it has concrete names (similar to variables)
    case DotTerm(sort, idx) => "•" +
      (idx match { case None => "" case Some(i) => "_" + i }) +
      (sort match { case Tuple(_, _) => sort.toString case _ => "" }) //@note will parse as Pair(Variable("Real"), ...), which has Sort sort
    case DifferentialSymbol(x)  => pp(x) + op(term).opcode
    case x: Variable            => x.asString
    case Differential(t)        => "(" + pp(t) + ")" + op(term).opcode
    //@note forcing parentheses around numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x. Alternatively could add space after unary Neg.
    case Number(n)              => "(" + n.bigDecimal.toPlainString + ")"
    case FuncOf(f, c)           => f.asString + "(" + pp(c) + ")"
    // special notation
    case Pair(l, r)             => "(" + pp(l) + op(term).opcode + pp(r) + ")"
    case UnitFunctional(name,space,sort) => name + "(" + space + ")"
    //@note all remaining unary operators are prefix, see [[OpSpec]]
    case t: UnaryCompositeTerm  => op(t).opcode + "(" + pp(t.child) + ")"
    //@note all binary operators are infix, see [[OpSpec]]
    case t: BinaryCompositeTerm =>
      "(" + pp(t.left) + ")" + op(t).opcode + "(" + pp(t.right) + ")"
  }

  private def pp(formula: Formula): String = formula match {
    case True|False|DotFormula  => op(formula).opcode
    case PredOf(p, c)           => p.asString + "(" + pp(c) + ")"
    case PredicationalOf(p, c)  => p.asString + "{" + pp(c) + "}"
    case f: ComparisonFormula   => "(" + pp(f.left) + ")" + LEXSPACE + op(formula).opcode + LEXSPACE + "(" + pp(f.right) + ")"
    case DifferentialFormula(g) => "(" + pp(g) + ")" + op(formula).opcode
    case f: Quantified          => op(formula).opcode + " " + f.vars.map(pp).mkString(",") + " " + "(" + pp(f.child) + ")"
    case f: Box                 => "[" + pp(f.program) + "]" + "(" + pp(f.child) + ")"
    case f: Diamond             => "<" + pp(f.program) + ">" + "(" + pp(f.child) + ")"
    case UnitPredicational(name,space) => name + "(" + space + ")"
    //@note all remaining unary operators are prefix, see [[OpSpec]]
    case t: UnaryCompositeFormula=> op(t).opcode + "(" + pp(t.child) + ")"
    //@note all binary operators are infix, see [[OpSpec]]
    case t: BinaryCompositeFormula=>
      "(" + pp(t.left) + ")" + op(t).opcode + "(" + pp(t.right) + ")"
  }

  private def pp(program: Program): String = program match {
    case a: ProgramConst        => statement(a.asString)
    case a: SystemConst         => statement(a.toString)
    case Assign(x, e)           => statement(pp(x) + op(program).opcode + pp(e))
    case AssignAny(x)           => statement(pp(x) + op(program).opcode)
    case Test(f)                => statement(op(program).opcode + "(" + pp(f) + ")")
    case ODESystem(ode, f)      => "{" + ppODE(ode) + op(program).opcode + pp(f) + "}"
    //@note unambiguously reparse as ODE not as equation that happens to involve a differential symbol.
    //@note This is only used in printing internal data structures, not user input.
    case ode: DifferentialProgram => "{" + ppODE(ode) + "}"
    //@note all remaining unary operators are prefix, see [[OpSpec]]
    case t: UnaryCompositeProgram => "{" + pp(t.child) + "}" + op(program).opcode
//    case t: Compose if OpSpec.statementSemicolon =>
//      //@note in statementSemicolon mode, suppress opcode of Compose since already after each statement
//      "{" + pp(t.left) + "}" + /*op(t).opcode + */ "{" + pp(t.right) + "}"
    //@note all binary operators are infix, see [[OpSpec]]
    case t: BinaryCompositeProgram =>
      "{" + pp(t.left) + "}" + op(t).opcode + "{" + pp(t.right) + "}"
  }

  private def ppODE(program: DifferentialProgram): String = program match {
    case a: DifferentialProgramConst => a.asString
    case AtomicODE(xp, e)       => pp(xp) + op(program).opcode + pp(e)
    case t: DifferentialProduct =>
      assert(op(t).assoc==RightAssociative && !t.left.isInstanceOf[DifferentialProduct], "differential products are always right-associative")
      ppODE(t.left) + op(t).opcode + ppODE(t.right)
  }


  /** Formatting the atomic statement s */
  protected def statement(s: String): String = if (statementSemicolon) s + ";" else s

}

/**
 * Vanilla: KeYmaera X Printer formats differential dynamic logic expressions
 * in KeYmaera X notation according to the concrete syntax of differential dynamic logic
 * with explicit statement end ``;`` operator.
  *
  * @example
 * Printing formulas to strings is straightforward using [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter.apply]]:
 * {{{
 * val pp = KeYmaeraXPrettyPrinter
 * // "x < -y"
 * val fml0 = Less(Variable("x"),Neg(Variable("y")))
 * val fml0str = pp(fml0)
 * // "true -> [x:=1;]x>=0"
 * val fml1 = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
 * val fml1str = pp(fml1)
 * }}}
 * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser]]
  * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
  * @see [[https://github.com/LS-Lab/KeYmaeraX-release/wiki/KeYmaera-X-Syntax-and-Informal-Semantics Wiki]]
  */
class KeYmaeraXPrinter extends BasePrettyPrinter {

  import OpSpec.op
  import OpSpec.statementSemicolon

  lazy val parser: KeYmaeraXParser.type = KeYmaeraXParser
  val fullPrinter: (Expression => String) = FullPrettyPrinter

  /** Pretty-print term to a string but without contract checking! */
  private[keymaerax] def stringify(expr: Expression) = expr match {
    case t: Term    => pp(HereP, t)
    case f: Formula => pp(HereP, f)
    case p: Program => pp(HereP, p)
    case f: Function => f.asString
  }

  /** True if negative numbers should get extra parentheses */
  private[parser] val negativeBrackets = true && OpSpec.negativeNumber

  /**@note The extra space disambiguates x<-7 as in x < (-7) from x REVIMPLY 7 as well as x<-(x^2) from x REVIMPLY ... */
  private val LEXSPACE: String = " "

  /** Pretty-print the operator of a term */
  protected def ppOp(expr: Expression): String = expr match {
    //@note in statementSemicolon mode, suppress opcode of Compose since already after each statement
    case _: Compose if OpSpec.statementSemicolon => ""
    case _ => op(expr).opcode
  }

  /** Pretty-print enclosing parentheses, braces, brackets etc. */
  protected def wrap(text: String, expr: Expression): String = expr match {
    case _: Box => "[" + text + "]"
    case _: Diamond => "<" + text + ">"
    case _: Program => "{" + text + "}"
    case _: PredOf => "(" + text + ")"
    case _: Pair => "(" + text + ")"
    case _: PredicationalOf => "{" + text + "}"
    case _ => throw new AssertionError("no parenthetical expression " + expr)
  }

  //@todo could add contract that TermAugmentor(original)(q) == term
  protected def pp(q: PosInExpr, term: Term): String = emit(q, term match {
    case Nothing       => ppOp(term)
    case DotTerm(sort, idx) => "•" +
        (idx match { case None => "" case Some(i) => "_" + i }) +
        (sort match { case Tuple(_, _) => sort.toString case _ => "" }) //@note will parse as Pair(Variable("Real"), ...), which has Sort sort
    case DifferentialSymbol(x)  => x.asString + ppOp(term)
    case x: Variable            => x.asString
    // disambiguate (-2)' versus (-(2))' versus ((-2))'
    case Differential(Number(n)) if negativeBrackets =>
      if (n < 0) "((" + n.bigDecimal.toPlainString + "))" + ppOp(term)
      else n.bigDecimal.toPlainString + ppOp(term)
    case Differential(t)        => "(" + pp(q++0, t) + ")" + ppOp(term)
      // special case forcing parentheses around numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x. Alternatively could add space after unary Neg.
    case Number(n)              => if (negativeBrackets) {
      if (n < 0) "(" + n.bigDecimal.toPlainString + ")"
      else n.bigDecimal.toPlainString
    } else n.bigDecimal.toPlainString
    case FuncOf(f, c)           => if (f.domain.isInstanceOf[Tuple]) f.asString + pp(q++0, c) else f.asString + "(" + pp(q++0, c) + ")"
    // special notation
    case p: Pair                =>
      //@todo create positions when flattening pairs
      /** Flattens pairs in right-associative way */
      def flattenPairs(e: Term): List[Term] = e match {
        case Pair(l, r) => l :: flattenPairs(r)
        case t => t :: Nil
      }
      val flattened = flattenPairs(p)
      // PosInExpr for a list [a,b,c,d] ~> .0, .1.0, .1.1.0, .1.1.1, which are the binary digits of [0,2,6,7] computed as [2^1-2, 2^2-2, 2^3-2, 2^3-1]
      val posInExprs = ListBuffer.empty[PosInExpr]
      for (i <- flattened.indices.takeRight(flattened.size-1)) {
        // (1<<i)-2 go right i-2 times, then go left
        posInExprs.append(PosInExpr(((1<<i)-2).toBinaryString.map(_.asDigit).toList))
      }
      posInExprs.append(PosInExpr(((1<<posInExprs.size)-1).toBinaryString.map(_.asDigit).toList))
      wrap(flattened.zipWithIndex.map({ case (p, i) => pp(q++posInExprs(i), p) }).mkString(ppOp(term)), term)
    case UnitFunctional(name,space,sort) => name + "(" + space + ")"
    // special case forcing to disambiguate between -5 as in the number (-5) as opposed to -(5). OpSpec.negativeNumber
    case t@Neg(Number(n))       => ppOp(t) + "(" + pp(q++0, Number(n)) + ")"
    // special case forcing space between unary negation and numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x.
    case t: Neg if !negativeBrackets => val c = pp(q++0, t.child)
      ppOp(t) + (if (c.charAt(0).isDigit) " " else "") + wrapChild(t, c)
    //@note all remaining unary operators are prefix, see [[OpSpec]]
    case t: UnaryCompositeTerm  => ppOp(t) + wrapChild(t, pp(q++0, t.child))
    //@note all binary operators are infix, see [[OpSpec]]
    case t: BinaryCompositeTerm =>
      wrapLeft(t, pp(q++0, t.left)) + ppOp(t) + wrapRight(t, pp(q++1, t.right))
  })

  protected def pp(q: PosInExpr, formula: Formula): String = emit(q, formula match {
    case True|False|DotFormula  => ppOp(formula)
    case PredOf(p, c)           => if (p.domain.isInstanceOf[Tuple]) p.asString + pp(q++0, c) else p.asString + "(" + pp(q++0, c) + ")"
    case PredicationalOf(p, c)  => p.asString + "{" + pp(q++0, c) + "}"
    // special case to disambiguate between x<-y as in x < -y compared to x REVIMPLY y
    case f: Less                => wrapLeft(f, pp(q++0, f.left)) + LEXSPACE + ppOp(formula) + LEXSPACE + wrapRight(f, pp(q++1, f.right))
    case f: ComparisonFormula   => wrapLeft(f, pp(q++0, f.left)) + ppOp(formula) + wrapRight(f, pp(q++1, f.right))
    case DifferentialFormula(g) => "(" + pp(q++0, g) + ")" + ppOp(formula)
    //@note the q position for variables is a little weird since it identifies the quantifier not the variable
    case f: Quantified          => ppOp(formula) + " " + f.vars.map(pp(q,_)).mkString(",") + " " + wrapChild(f, pp(q++0, f.child))
    case f: Box                 => wrap(pp(q++0, f.program), f) + wrapChild(f, pp(q++1, f.child))
    case f: Diamond             => wrap(pp(q++0, f.program), f) + wrapChild(f, pp(q++1, f.child))
    case UnitPredicational(name,space) => name + "(" + space + ")"
    //@note all remaining unary operators are prefix, see [[OpSpec]]
    case t: UnaryCompositeFormula=> ppOp(t) + wrapChild(t, pp(q++0, t.child))
    //@note all binary operators are infix, see [[OpSpec]]
    case t: BinaryCompositeFormula=>
      wrapLeft(t, pp(q++0, t.left)) + ppOp(t) + wrapRight(t, pp(q++1, t.right))
  })

  protected def pp(q: PosInExpr, program: Program): String = emit(q, program match {
    case a: ProgramConst        => statement(a.asString)
    case a: SystemConst         => statement(a.toString)
    case Assign(x, e)           => statement(pp(q++0, x) + ppOp(program) + pp(q++1, e))
    case AssignAny(x)           => statement(pp(q++0, x) + ppOp(program))
    case Test(f)                => statement(ppOp(program) + pp(q++0, f))
    //@todo avoid & true
    case ODESystem(ode, f)      => wrap(ppODE(q++0, ode) + (if (false && f==True) "" else ppOp(program) + pp(q++1, f)), program)
    //@note unambiguously reparse as ODE not as equation that happens to involve a differential symbol.
    //@note This is only used in printing internal data structures, not user input (ODESystem case catches user input).
    //@note no positional change since ODESystem already descended into child position
    case ode: DifferentialProgram => wrap(ppODE(q, ode), program)
    //@note forced parentheses in grammar for loops and duals
    case t: UnaryCompositeProgram => wrap(pp(q++0, t.child), program) + ppOp(program)
    case t: Compose => pwrapLeft(t, pp(q++0, t.left)) + ppOp(t) + pwrapRight(t, pp(q++1, t.right))
    case t: BinaryCompositeProgram => pwrapLeft(t, pp(q++0, t.left)) + ppOp(t) + pwrapRight(t, pp(q++1, t.right))
  })

  protected def ppODE(q: PosInExpr, program: DifferentialProgram): String = emit(q, program match {
    case a: DifferentialProgramConst => a.asString
    case AtomicODE(xp, e)       => pp(q++0, xp) + ppOp(program) + pp(q++1, e)
    case t: DifferentialProduct =>
      assert(op(t).assoc==RightAssociative && !t.left.isInstanceOf[DifferentialProduct], "differential products are always right-associative")
      ppODE(q++0, t.left) + ppOp(t) + ppODE(q++1, t.right)
  })


  // parentheses wrapping and emission

  /** Wrap ``childPrint`` for ``t.child`` in parentheses if they are not implicit. */
  protected def wrapChild(t: UnaryComposite, childPrint: String): String = "(" + childPrint + ")"
  /** Wrap ``childPrint`` for ``t.child`` in parentheses if they are not implicit. */
  protected def wrapChild(t: Quantified, childPrint: String): String = "(" + childPrint + ")"
  /** Wrap ``childPrint`` for ``t.child`` in parentheses if they are not implicit. */
  protected def wrapChild(t: Modal, childPrint: String): String = "(" + childPrint + ")"

  /** Wrap ``leftPrint`` for ``t.left`` in parentheses if they are not implicit. */
  protected def wrapLeft(t: BinaryComposite, leftPrint: String): String = "(" + leftPrint + ")"
  /** Wrap ``rightPrint`` for ``t.right`` in parentheses if they are not implicit. */
  protected def wrapRight(t: BinaryComposite, rightPrint: String): String = "(" + rightPrint + ")"

  /** Wrap ``leftPrint`` for ``t.left`` in program parentheses if they are not implicit. */
  protected def pwrapLeft(t: BinaryComposite/*Differential/Program*/, leftPrint: String): String =
    "{" + leftPrint + "}"
  /** Wrap ``rightPrint`` for ``t.right`` in program parentheses if they are not implicit. */
  protected def pwrapRight(t: BinaryComposite/*Differential/Program*/, rightPrint: String): String =
    "{" + rightPrint + "}"

  /** Emit the string ``s`` as a result of the pretty-printer for the expression at position ``q`` */
  protected def emit(q: PosInExpr, s: String): String = s

  /** Formatting the atomic statement s */
  protected def statement(s: String): String = if (statementSemicolon) s + ";" else s

}

// additional pretty printers


/** Fully parenthesized pretty printer that is functionally equivalent to [[FullPrettyPrinter]] */
object FullPrettyPrinter0 extends KeYmaeraXPrinter {
  //@note no contract to avoid recursive checking of contracts in error messages of KeYmaeraXPrinter.apply
  override def apply(expr: Expression): String = stringify(expr)
}

/**
  * KeYmaera X Printer base class formatting based on parentheses skipping decisions.
  *
  * @author Andre Platzer
  */
abstract class KeYmaeraXSkipPrinter extends KeYmaeraXPrinter {
  protected override def wrapChild(t: UnaryComposite, childPrint: String): String =
    if (skipParens(t)) childPrint else "(" + childPrint + ")"
  protected override def wrapChild(t: Quantified, childPrint: String): String =
    if (skipParens(t)) childPrint else "(" + childPrint + ")"
  protected override def wrapChild(t: Modal, childPrint: String): String =
    if (skipParens(t)) childPrint else "(" + childPrint + ")"

  protected override def wrapLeft(t: BinaryComposite, leftPrint: String): String =
    if (skipParensLeft(t)) leftPrint else "(" + leftPrint + ")"
  protected override def wrapRight(t: BinaryComposite, rightPrint: String): String =
    if (skipParensRight(t)) rightPrint else "(" + rightPrint + ")"

  protected override def pwrapLeft(t: BinaryComposite/*Differential/Program*/, leftPrint: String): String =
    if (skipParensLeft(t)) leftPrint else "{" + leftPrint + "}"
  protected override def pwrapRight(t: BinaryComposite/*Differential/Program*/, rightPrint: String): String =
    if (skipParensRight(t)) rightPrint else "{" + rightPrint + "}"

  /**
    * Whether parentheses around ``t.child`` can be skipped because they are implicit.
    * @see [[wrapChild()]]
    */
  protected def skipParens(t: UnaryComposite): Boolean

  /**
    * Whether parentheses around ``t.child`` can be skipped because they are implicit.
    * @see [[wrapChild()]]
    */
  protected def skipParens(t: Quantified): Boolean

  /**
    * Whether parentheses around ``t.child`` can be skipped because they are implicit.
    * @see [[wrapChild()]]
    */
  protected def skipParens(t: Modal): Boolean

  /**
    * Whether parentheses around ``t.left`` can be skipped because they are implicit.
    * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
    * @see [[wrapLeft()]]
    */
  protected def skipParensLeft(t: BinaryComposite): Boolean

  /**
    * Whether parentheses around ``t.right`` can be skipped because they are implicit.
    * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
    * @see [[wrapRight()]]
    */
  protected def skipParensRight(t: BinaryComposite): Boolean

}

/**
  * Precedence-based: KeYmaera X Pretty Printer formats differential dynamic logic expressions with compact brackets
  * in KeYmaera X notation according to the concrete syntax of differential dynamic logic
  * with explicit statement end ``;`` operator.
  * @author Andre Platzer
  * @todo Augment with ensures postconditions that check correct reparse non-recursively.
  * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
  */
class KeYmaeraXPrecedencePrinter extends KeYmaeraXSkipPrinter {
  /** @inheritdoc */
  protected override def skipParens(t: UnaryComposite): Boolean = op(t.child) <= op(t)

  /** @inheritdoc */
  protected override def skipParens(t: Quantified): Boolean = op(t.child) <= op(t)

  /** @inheritdoc */
  protected override def skipParens(t: Modal): Boolean = op(t.child) <= op(t)

  /**
    * Whether parentheses around ``t.left`` can be skipped because they are implied.
    * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
    */
  protected override def skipParensLeft(t: BinaryComposite): Boolean =
    op(t.left) < op(t) || op(t.left) <= op(t) && op(t).assoc == LeftAssociative && op(t.left).assoc == LeftAssociative

  /**
    * Whether parentheses around ``t.right`` can be skipped because they are implied.
    * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
    */
  protected override def skipParensRight(t: BinaryComposite): Boolean =
    op(t.right) < op(t) || op(t.right) <= op(t) && op(t).assoc == RightAssociative && op(t.right).assoc == RightAssociative

}

/**
  * Weighted precedence-based: KeYmaera X Pretty Printer formats differential dynamic logic expressions with compact brackets
  * in KeYmaera X notation according and extra space weighted according to the concrete syntax of differential dynamic logic
  * with explicit statement end ``;`` operator.
  *
  * @author Andre Platzer
  * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
  */
@deprecated("Use PrettierPrinter instead")
class KeYmaeraXWeightedPrettyPrinter extends KeYmaeraXPrecedencePrinter {

  // eloquent space if no parentheses
  protected override def wrapChild(t: Modal, childPrint: String): String =
    if (skipParens(t)) " " + childPrint else "(" + childPrint + ")"

  protected override def wrapLeft(t: BinaryComposite, leftPrint: String): String =
    if (skipParensLeft(t)) spaceLeft(t, leftPrint) else spaceLeft(t, "(" + leftPrint + ")")
  protected override def wrapRight(t: BinaryComposite, rightPrint: String): String =
    if (skipParensRight(t)) spaceRight(t, rightPrint) else spaceRight(t, "(" + rightPrint + ")")

  protected override def pwrapLeft(t: BinaryComposite/*Differential/Program*/, leftPrint: String): String =
    if (skipParensLeft(t)) spaceLeft(t, leftPrint) else spaceLeft(t, "{" + leftPrint + "}")
  protected override def pwrapRight(t: BinaryComposite/*Differential/Program*/, rightPrint: String): String =
    if (skipParensRight(t)) spaceRight(t, rightPrint) else spaceRight(t, "{" + rightPrint + "}")

  protected def spaceLeft(t: BinaryComposite, leftPrint: String): String =
    if (skipParensLeft(t)) leftPrint + (" " * weight(t.left, t)) else leftPrint
  protected def spaceRight(t: BinaryComposite, rightPrint: String): String =
    if (skipParensRight(t)) (" " * weight(t.right, t)) + rightPrint else rightPrint

  protected def weight(sub: Expression, par: BinaryComposite): Int = {
    val prec = op(par).prec
    if (prec >= 200)
      // programs are formatted relative to one another not with their ridiculously large prec
      (prec-150) / 50
    else
      prec / 50
  }

  private def weight2(sub: Expression, par: BinaryComposite): Int = {
    val relative = Math.abs(op(sub).prec - op(par).prec)
    if (relative <= 10 /*|| !(binaryOfKind(par.left, par) || binaryOfKind(par.right, par))*/) 0
    else relative / 20
  }

  /** Whether sub is a binary composite of the same kind that par is a binary composite */
  private def binaryOfKind(sub: Expression, par: BinaryComposite): Boolean = par.kind match {
    case TermKind => sub.isInstanceOf[BinaryCompositeTerm]
    case FormulaKind => sub.isInstanceOf[BinaryCompositeFormula]
    case ProgramKind => sub.isInstanceOf[BinaryCompositeProgram]
    case DifferentialProgramKind => sub.isInstanceOf[DifferentialProduct]
    case FunctionKind => assert(false, "No completed expressions of FunctionKind can be constructed"); ???
    case ExpressionKind => assert(false, "No expressions of ExpressionKind can be constructed"); ???
  }

  private def weight1(sub: Expression, par: BinaryComposite): Int = {
    val relative = Math.abs(op(sub).prec - op(par).prec)
    val imbalance = Math.abs(op(par.left).prec - op(par.right).prec)
    //@todo this implementation probably needs more thought
    if (relative<10 || imbalance<10) 0
    else (relative + 19) / 20    // rounded-up division
  }

  override def stringify(e: Expression): String = super.stringify(e)
}

/**
  * Vertical layout using an implementation based on Wadler's "A Prettier Printer"
  * @author Fabian Immler
  * @see [[http://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf]]
  */
class KeYmaeraXPrettierPrinter(margin: Int) extends KeYmaeraXPrecedencePrinter {

  /** Encloses document `doc` between strings `s1` and `s2`, preferably rendered in a single line. */
  protected def encloseText(s1: String, doc: Doc, s2: String): Doc = doc.tightBracketBy(Doc.text(s1), Doc.text(s2))

  protected def wrapDoc(doc: Doc, expr: Expression): Doc = expr match {
    case _: Box => encloseText("[", doc,"]")
    case _: Diamond => encloseText("<", doc,">")
    case _: Program => encloseText("{", doc,"}")
    case _: PredOf => encloseText("(", doc,")")
    case _: Pair => encloseText("(", doc,")")
    case _: PredicationalOf => encloseText("{", doc,"}")
    case _ => throw new AssertionError("no parenthetical expression " + expr)
  }

  protected def wrapChildDoc(t: UnaryComposite, doc: Doc): Doc =
    if (skipParens(t)) doc else encloseText("(", doc,")")
  protected def wrapChildDoc(t: Quantified, doc: Doc): Doc =
    if (skipParens(t)) doc else encloseText("(", doc,")")
  protected def wrapChildDoc(t: Modal, doc: Doc): Doc =
    if (skipParens(t)) doc else encloseText("(", doc,")")

  protected def wrapLeftDoc(t: BinaryComposite, doc: Doc): Doc =
    if (skipParensLeft(t)) doc else encloseText("(", doc,")")
  protected def wrapRightDoc(t: BinaryComposite, doc: Doc): Doc =
    if (skipParensRight(t)) doc else encloseText("(", doc,")")

  protected def pwrapLeftDoc(t: BinaryComposite/*Differential/Program*/, doc: Doc): Doc =
    if (skipParensLeft(t)) doc else encloseText("{", doc,"}")
  protected def pwrapRightDoc(t: BinaryComposite/*Differential/Program*/, doc: Doc): Doc =
    if (skipParensRight(t)) doc else encloseText("{", doc,"}")

  protected def docOf(term: Term): Doc = term match {
    case Differential(t)        => encloseText("(", docOf(t),")" + ppOp(term))
    case FuncOf(f, Nothing)     => Doc.text(f.asString + "()")
    case FuncOf(f, c: Pair)     => (Doc.text(f.asString) + Doc.lineBreak + docOf(c)).grouped
    case FuncOf(f, c)           => (Doc.text(f.asString) + encloseText("(", Doc.lineBreak + docOf(c), ")").nested(2)).grouped
    case p: Pair                =>
      /** Flattens pairs in right-associative way */
      def flattenPairs(e: Term): List[Term] = e match {
        case Pair(l, r) => l :: flattenPairs(r)
        case t => t :: Nil
      }
      wrapDoc((Doc.lineBreak + flattenPairs(p).map(docOf).reduce[Doc]({ case (a, b) => a + Doc.text(ppOp(term)) + Doc.lineBreak + b + Doc.lineBreak })).nested(2).grouped, term)
    case Neg(Number(_))         => Doc.text(pp(HereP, term))
    case t: Neg if !negativeBrackets =>
      val c = pp(HereP, t.child)
      Doc.text(ppOp(t) + (if (c.charAt(0).isDigit) " " else "")) + wrapChildDoc(t, docOf(t.child)).grouped
    case t: UnaryCompositeTerm  => (Doc.text(ppOp(t)) + wrapChildDoc(t, docOf(t.child))).grouped
    case t@Power(base, exp)     => (wrapLeftDoc(t, docOf(base)) + Doc.text(ppOp(t)) + wrapRightDoc(t, docOf(exp))).grouped
    case t: BinaryCompositeTerm => (wrapLeftDoc(t, docOf(t.left)) + Doc.space + Doc.text(ppOp(t)) + Doc.line + wrapRightDoc(t, docOf(t.right))).grouped
    case _ => Doc.text(pp(HereP, term))
  }

  protected def docOf(formula: Formula): Doc = formula match {
    case True|False|DotFormula  => Doc.text(ppOp(formula))
    case PredOf(p, c: Pair)     => (Doc.text(p.asString) + Doc.lineBreak + docOf(c)).grouped
    case PredOf(p, c)           => (Doc.text(p.asString) + Doc.lineBreak + encloseText("(", docOf(c), ")").nested(2)).grouped
    case PredicationalOf(p, c)  => (Doc.text(p.asString) + Doc.lineBreak + encloseText("{", docOf(c), "}").nested(2)).grouped
    case f: ComparisonFormula   => (wrapLeftDoc(f, docOf(f.left)) + Doc.space + Doc.text(ppOp(formula)) + Doc.line + wrapRightDoc(f, docOf(f.right))).grouped
    case DifferentialFormula(g) => encloseText("(", docOf(g), ")" + ppOp(formula))
    // prints quantifiers with comma-separated list of variables
    case f: Quantified          => (Doc.text(ppOp(formula)) + Doc.space + Doc.intercalate(Doc.comma+Doc.space, f.vars.map(docOf(_))) +
      (Doc.line + wrapChildDoc(f, docOf(f.child))).nested(2)).grouped
    case f: Box                 => (wrapDoc(docOf(f.program), f) + (Doc.lineBreak + wrapChildDoc(f, docOf(f.child))).nested(2)).grouped
    case f: Diamond             => (wrapDoc(docOf(f.program), f) + (Doc.lineBreak + wrapChildDoc(f, docOf(f.child))).nested(2)).grouped
    case UnitPredicational(name,space) => Doc.text(name) + encloseText("(", Doc.text(space.toString), ")")
    case t: UnaryCompositeFormula => (Doc.text(ppOp(t)) + wrapChildDoc(t, docOf(t.child))).grouped
    case t: BinaryCompositeFormula=> (wrapLeftDoc(t, docOf(t.left)) + Doc.space + Doc.text(ppOp(t)) + Doc.line + wrapRightDoc(t, docOf(t.right))).grouped
  }

  /** Statement with closing ; */
  protected def statementDoc(s: Doc): Doc = if (OpSpec.statementSemicolon) s + Doc.text(";") else s

  protected def docOf(program: Program): Doc = program match {
    case a: ProgramConst        => statementDoc(Doc.text(a.asString))
    case a: SystemConst         => statementDoc(Doc.text(a.asString))
    case Assign(x, e)           => statementDoc(docOf(x) + Doc.text(ppOp(program)) + (Doc.lineBreak + docOf(e)).nested(2)).grouped
    case AssignAny(x)           => statementDoc(docOf(x) + Doc.text(ppOp(program)))
    case Test(f)                => statementDoc(Doc.text(ppOp(program)) + docOf(f).nested(2)).grouped
    case ODESystem(ode, True) => wrapDoc(docOfODE(ode), program).grouped
    case ODESystem(ode, f) => wrapDoc(docOfODE(ode) + Doc.space + Doc.text(ppOp(program)) + Doc.line + docOf(f), program).grouped
    case ode: DifferentialProgram => (Doc.line + wrapDoc(docOfODE(ode), program) + Doc.line).grouped
    //@note all remaining unary operators are postfix, see [[OpSpec]]
    case t: UnaryCompositeProgram => (wrapDoc(docOf(t.child), program) + Doc.text(ppOp(program))).grouped
    case t: Compose => (pwrapLeftDoc(t, docOf(t.left)) + Doc.line + Doc.text(ppOp(t)) + pwrapRightDoc(t, docOf(t.right))).grouped
    //@note all remaining binary operators are infix, see [[OpSpec]]
    case t: BinaryCompositeProgram => (pwrapLeftDoc(t, docOf(t.left)) + Doc.line + Doc.text(ppOp(t)) + Doc.line + pwrapRightDoc(t, docOf(t.right))).grouped
  }

  protected def docOfODE(program: DifferentialProgram): Doc = program match {
    case a: DifferentialProgramConst => Doc.text(a.asString)
    case AtomicODE(xp, e)       => docOf(xp) + Doc.text(ppOp(program)) + docOf(e)
    case t: DifferentialProduct =>
      assert(op(t).assoc == RightAssociative && !t.left.isInstanceOf[DifferentialProduct], "differential products are always right-associative")
      docOfODE(t.left) + Doc.text(ppOp(t)) + Doc.line + docOfODE(t.right)
  }

  override def stringify(expr: Expression): String = {
    val doc = expr match {
      case t: Term    => docOf(t)
      case f: Formula => docOf(f)
      case p: Program => docOf(p)
      case f: Function => Doc.text(f.asString)
    }
    doc.render(margin)
  }

  def docOf(seq: Sequent) : Doc =
    Doc.intercalate(Doc.line, (1 to seq.ante.length).map(i => Doc.text(-i + ": ") + (Doc.line + docOf(seq.ante(i - 1))).nested(2))) +
      Doc.line + Doc.text(" ==> ") + Doc.line +
      Doc.intercalate(Doc.line, (1 to seq.succ.length).map(i => Doc.text(+i + ": ") + (Doc.line + docOf(seq.succ(i - 1))).nested(2)))

  override def stringify(seq: Sequent): String = docOf(seq).render(margin)

  def docOf(prv: ProvableSig): Doc =
    Doc.text("Conclusion:") + (Doc.line + docOf(prv.conclusion)).nested(2) +
      Doc.line + Doc.text(prv.subgoals.length + " subgoals" + (if (prv.subgoals.length == 0) "." else ":")) + Doc.line +
      Doc.intercalate(Doc.line, prv.subgoals.zipWithIndex.map{case (seq, i) =>
        Doc.text("Subgoal " + i + ": ") + (Doc.line + docOf(seq).nested(2))})

  def stringify(prv: ProvableSig): String = docOf(prv).render(margin)

}
