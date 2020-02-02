package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.core._

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
  def asExpr: Expression = KeYmaeraXParser(s)

  def asTerm: Term = KeYmaeraXParser.termParser(s)

  def asNamedSymbol: NamedSymbol = KeYmaeraXParser(s) match {
    case ns: NamedSymbol => ns
    case _ => throw new IllegalArgumentException("Input " + s + " is not a named symbol")
  }

  def asVariable: Variable = KeYmaeraXParser.termParser(s) match {
    case v: Variable => v
    case _ => throw new IllegalArgumentException("Input " + s + " is not a variable")
  }

  def asFunction: Function = KeYmaeraXParser.termParser(s) match {
    case v: Variable  => Function(v.name, v.index, Unit, Real, interpreted=false)
    case FuncOf(f, _) => f
    case _ => throw new IllegalArgumentException("Input " + s + " is not a function")
  }

  def asFormula: Formula = KeYmaeraXParser.formulaParser(s)

  def asProgram: Program = KeYmaeraXParser.programParser(s)

  def asDifferentialProgram: DifferentialProgram = KeYmaeraXParser.differentialProgramParser(s)

  def asTactic : BelleExpr = BelleParser(s)

  //If a split failed to parse, merge it with the next formula and try again because it might have been split incorrectly
  //e.g. max((a,b)) would be incorrectly split
  private def smartFmlSplit(acc:String,ls:List[String]) : List[Formula] = {
    ls match {
      case Nil =>
        if (acc!="")
          List(KeYmaeraXParser.formulaParser(acc))
        else
          Nil
      case (l::lss) =>
        if(l == "") smartFmlSplit(acc,lss)
        else {
          try {
            KeYmaeraXParser.formulaParser(acc + l) :: smartFmlSplit("", lss)
          }
          catch {
            case e: ParseException =>
              smartFmlSplit(acc + l + ",", lss)
          }
        }
    }
  }

  def asSequent: Sequent = {
    val (ante::succ::Nil) = s.split("==>").map(_.trim()).toList
    //println("parsing",ante,succ)
    val res = Sequent(
      smartFmlSplit("",ante.split(",(?![^{]*})").toList).toIndexedSeq,
      smartFmlSplit("",succ.split(",(?![^{]*})").toList).toIndexedSeq
    )
    res
  }

  /** Converts a string `what ~> repl` into a substitution pair. */
  def asSubstitutionPair: SubstitutionPair = {
    val exprs = s.split("~>")
    assert(exprs.size == 2, "Expected substitution pair of shape what ~> repl, but got " + s)
    val repl = KeYmaeraXParser(exprs(1))
    val what =
      if (repl.kind == FormulaKind) KeYmaeraXParser.formulaParser(exprs(0))
      else if (repl.kind == TermKind) KeYmaeraXParser.termParser(exprs(0))
      else KeYmaeraXParser.programParser(exprs(0))
    SubstitutionPair(what, repl)
  }
}