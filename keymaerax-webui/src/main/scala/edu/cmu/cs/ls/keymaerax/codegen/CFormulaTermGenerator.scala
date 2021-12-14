/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.Declaration

/**
  * Conversion of names.
  * @author Stefan Mitsch
  * @author Ran Ji
  */
object CFormulaTermGenerator {
  /** C Identifier corresponding to a NamedSymbol */
  def nameIdentifier(s: NamedSymbol): String = s match {
    case _: Function | _: Variable => s.name + s.index.map("_" + _).getOrElse("")
    case _ => throw new CodeGenerationException("Unsupported named symbol " + s.prettyString)
  }

  /** Prints a struct declaration named `structName` with a field for each of the names in `vars`. */
  def printStructDeclaration[T <: NamedSymbol](structName: String, vars: Set[T], comment: String): String = {
    // stable ordering by NamedSymbol.compare
    val fields = vars.toList.sorted[NamedSymbol].map({
      case x: Variable => printSort(x.sort) + " " + nameIdentifier(x) + ";"
      case f: Function =>
        assert(!CodeGenerator.isInterpreted(f), "Parameter must not be an interpreted function")
        assert(f.domain == Unit, "If declared as function, parameter must have domain Unit, but has " + f.domain)
        printSort(f.sort) + " " + nameIdentifier(f) + ";"
      case _ => None
    }).mkString("\n  ")
    val structBody = if (vars.isEmpty) "" else "{\n  " + fields + "\n} "
    s"/** $comment */\ntypedef struct $structName $structBody$structName;\n\n"
  }

  /** Print sort `s` as a C type. */
  def printSort(s: Sort): String = s match {
    case Unit => "void"
    case Real => "long double"
    case Bool => "bool"
    case Tuple(l, r) => ??? //printSort(l) + ", " + printSort(r)
    case _ => s.toString
  }
}


/**
  * Generates formula and term evaluation C code. `termContainer` configures the location where primitive terms are
  * looked up (e.g., structs).
  * @author Stefan Mitsch
  * @author Ran Ji
  */
class CFormulaTermGenerator(termContainer: Expression => String, defs: Declaration) extends FormulaTermGenerator(termContainer, defs) {
  override def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable],
                     modelName: String): (String, String) = expr match {
    case f: Formula if f.isFOL => CPrettyPrinter(compileFormula(f))
    case t: Term => CPrettyPrinter(compileTerm(t))
  }

  /** @inheritdoc */
  override def nameIdentifier(s: NamedSymbol): String = CFormulaTermGenerator.nameIdentifier(s)

  /** @inheritdoc */
  override def printSort(s: Sort): String = CFormulaTermGenerator.printSort(s)
}
