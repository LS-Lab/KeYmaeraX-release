package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.UnificationMatch

/**
 * Implicit conversions from strings into core data structures.
 * Created by smitsch on 1/8/15.
 * @author Stefan Mitsch
 * @author Andre Platzer
 */
object StringConverter {
  import scala.language.implicitConversions
  implicit def StringToStringConverter(s: String): StringConverter = new StringConverter(s)
}

class StringConverter(val s: String) {
  def asExpr: Expression = Parser(s)

  def asTerm: Term = Parser.parser.termParser(s)

  def asNamedSymbol: NamedSymbol = Parser(s) match {
    case ns: NamedSymbol => ns
    case _ => throw new IllegalArgumentException("Input " + s + " is not a named symbol")
  }

  def asVariable: Variable = Parser.parser.termParser(s) match {
    case v: Variable => v
    case _ => throw new IllegalArgumentException("Input " + s + " is not a variable")
  }

  def asFunction: Function = Parser.parser.termParser(s) match {
    case v: Variable  => Function(v.name, v.index, Unit, Real, interpreted=false)
    case FuncOf(f, _) => f
    case _ => throw new IllegalArgumentException("Input " + s + " is not a function")
  }

  def asFormula: Formula = Parser.parser.formulaParser(s)

  def asProgram: Program = Parser.parser.programParser(s)

  def asDifferentialProgram: DifferentialProgram = Parser.parser.differentialProgramParser(s)

  def asTactic : BelleExpr = BelleParser(s)

  //If a split failed to parse, merge it with the next formula and try again because it might have been split incorrectly
  //e.g. max((a,b)) would be incorrectly split
  private def smartFmlSplit(acc:String,ls:List[String]) : List[Formula] = {
    ls match {
      case Nil =>
        if (acc!="")
          List(Parser.parser.formulaParser(acc))
        else
          Nil
      case l::lss =>
        if (l == "") smartFmlSplit(acc,lss)
        else {
          try {
            Parser.parser.formulaParser(acc + l) :: smartFmlSplit("", lss)
          } catch {
            case _: ParseException => smartFmlSplit(acc + l + ",", lss)
          }
        }
    }
  }

  def asSequent: Sequent = {
    val splitter = ",(?![^{]*})"
    val turnStileIdx = s.indexOf(TURNSTILE.img)
    val ante::succ::Nil =
      if (turnStileIdx >= 0) {
        val (ante, succ) = s.splitAt(turnStileIdx)
        List(
          ante.trim.split(splitter).filter(_.nonEmpty).toList,
          succ.trim.stripPrefix(TURNSTILE.img).trim.split(splitter).filter(_.nonEmpty).toList)
      } else throw new IllegalArgumentException("String " + s + " is not a sequent (must contain turnstile ==>)")
    Sequent(
      smartFmlSplit("",ante).toIndexedSeq,
      smartFmlSplit("",succ).toIndexedSeq
    )
  }

  /** Converts a string `what ~> repl` or `(what ~> repl)` into a substitution pair. */
  def asSubstitutionPair: SubstitutionPair = {
    val exprs =
      if (s.startsWith("(") && s.endsWith(")")) s.stripPrefix("(").stripSuffix(")").split("~>")
      else s.split("~>")
    assert(exprs.size == 2, "Expected substitution pair of shape what ~> repl, but got " + s)
    val repl = Parser(exprs(1))
    val what =
      if (repl.kind == FormulaKind) Parser.parser.formulaParser(exprs(0))
      else if (repl.kind == TermKind) Parser.parser.termParser(exprs(0))
      else Parser.parser.programParser(exprs(0))
    UnificationMatch(what, repl).usubst.subsDefsInput.head
  }
}