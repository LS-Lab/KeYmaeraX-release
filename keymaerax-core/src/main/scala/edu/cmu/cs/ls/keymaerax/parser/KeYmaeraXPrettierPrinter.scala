/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Assign, AssignAny, AtomicODE, BinaryComposite, BinaryCompositeFormula, BinaryCompositeProgram, BinaryCompositeTerm, Box, ComparisonFormula, Compose, Diamond, Differential, DifferentialFormula, DifferentialProduct, DifferentialProgram, DifferentialProgramConst, DotFormula, Expression, False, Formula, FuncOf, Function, Modal, Neg, Nothing, Number, ODESystem, Pair, Power, PredOf, PredicationalOf, Program, ProgramConst, Quantified, Sequent, SystemConst, Term, Test, True, UnaryComposite, UnaryCompositeFormula, UnaryCompositeProgram, UnaryCompositeTerm, UnitPredicational}
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr.HereP
import edu.cmu.cs.ls.keymaerax.parser.OpSpec.op
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.typelevel.paiges.Doc

import scala.collection.immutable.{List, Nil}


/**
  * Vertical layout using an implementation based on Wadler's "A Prettier Printer"
  *
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
    case Differential(t@Number(n)) if negativeBrackets =>
      if (n < 0) encloseText("((", Doc.text(n.bigDecimal.toPlainString), "))" + ppOp(term))
      else encloseText("(", docOf(t), ")" + ppOp(term))
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
    case t@Neg(n: Number) if !negativeBrackets => Doc.text(ppOp(t) + "(" + pp(HereP, n) + ")")
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
    Doc.intercalate(Doc.line, (1 to seq.ante.length).map(i => Doc.text(s"${-i}: ") + (Doc.line + docOf(seq.ante(i - 1))).nested(2))) +
      Doc.line + Doc.text(" ==> ") + Doc.line +
      Doc.intercalate(Doc.line, (1 to seq.succ.length).map(i => Doc.text(s"$i: ") + (Doc.line + docOf(seq.succ(i - 1))).nested(2)))

  override def stringify(seq: Sequent): String = docOf(seq).render(margin)

  def docOf(prv: ProvableSig): Doc =
    Doc.text("Conclusion:") +
      (Doc.line + docOf(prv.conclusion)).nested(2) +
      Doc.line +
      Doc.text(s"${prv.subgoals.length} subgoals" + (if (prv.subgoals.isEmpty) "." else ":")) +
      Doc.line +
      Doc.intercalate(Doc.line, prv.subgoals.zipWithIndex.map{case (seq, i) =>
        Doc.text(s"Subgoal $i: ") + (Doc.line + docOf(seq).nested(2))})

  def stringify(prv: ProvableSig): String = docOf(prv).render(margin)

}
