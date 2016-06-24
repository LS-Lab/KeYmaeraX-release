/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
/**
  * @note Code Review: 2016-06-01
  */
package edu.cmu.cs.ls.keymaerax.tools

// favoring immutable Seqs
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq
import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.MExpr

import scala.math.BigDecimal


/**
 * Handles conversion to/from Mathematica.
 *
 * TODO-nrf assertion that maskName and removeMask are inverses (compose to
 * id).
 *
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
private object MathematicaNameConversion {
  private val PREFIX = "kyx`"
  private val SEP    = "$i$"
  //@todo Code Review: disallow $ in names
  //@solution: insist in maskIdentifier
  private val MUNDERSCORE = "$u$" //Mathematica Underscore

  private def regexOf(s: String) = {
    s.replace("$", "\\$")
  }

  private def maskIdentifier(name: String): String = {
    //Ensure that none of the "special" strings occur in the variable name.
    insist(!name.contains("\\$"), "Character '$' not allowed in variable names")
    //@note double-check with all separators
    insist(!name.contains(MUNDERSCORE), "String '" + MUNDERSCORE + "' not allowed in variable names")
    insist(!name.contains(PREFIX), "String '" + PREFIX + "' not allowed in variable names")
    insist(!name.contains(SEP), "String '" + SEP + "' not allowed in variable names")

    name.replace("_", MUNDERSCORE)
  }


  def toMathematica(ns: NamedSymbol): MExpr = {
    //The identifier (portion of name excluding index) has one of the forms:
    //   name (for external functions)
    //   KeYmaera + name
    val identifier : String = ns match {
      //@note special function
      //@todo Code Review: handle interpreted functions properly, handle name conflicts
      case Function("abs",None,Real,Real) => "Abs"
      case Function("Abs",None,Real,Real) => throw new IllegalArgumentException("Refuse translating Abs to Mathematica to avoid confusion with abs")
      case Function("min",None,Tuple(Real,Real),Real) => "Min"
      case Function("Min",None,Tuple(Real,Real),Real) => throw new IllegalArgumentException("Refuse translating Min to Mathematica to avoid confusion with min")
      case Function("max",None,Tuple(Real,Real),Real) => "Max"
      case Function("Max",None,Tuple(Real,Real),Real) => throw new IllegalArgumentException("Refuse translating Max to Mathematica to avoid confusion with max")
      case Function(name, _, _, _) => PREFIX + maskIdentifier(name)
      case Variable(name, _, _) => PREFIX + maskIdentifier(name)
    }

    //Add the index if it exists.
    val fullName: String   = ns.index match {
      case Some(idx) => identifier + SEP + idx
      case None      => identifier
    }
    new MExpr(com.wolfram.jlink.Expr.SYMBOL, fullName)
  } ensuring (r => r.symbolQ(), "symbol names expected as result")

  ////
  // toKeYmaera section. We decompose by function vs. variable. In each case, we
  // decompose based upon the possible forms of the name:
  // PREFIX + base + SEP + index ---> name + index
  // PREFIX + base               ---> name only
  // base                        ---> special function
  ///
  def toKeYmaera(e: MExpr): NamedSymbol = {
    if (e.args.isEmpty) {
      val (name, index) = unmaskName(e)
      Variable(name, index, Real)
    } else unmaskName(e.head()) match {
      //@note special function
      case ("Abs", None) => Function("abs", None, Real, Real)
      case ("Min", None) => Function("min", None, Tuple(Real, Real), Real)
      case ("Max", None) => Function("max", None, Tuple(Real, Real), Real)
      case ("Apply", None) =>
        // nary functions
        val fnName = unmaskName(e.args().head)
        assert(e.args().tail.length == 1)
        val fnDomain = convertFunctionDomain(e.args().tail.head)
        Function(fnName._1, fnName._2, fnDomain, Real)
      case (name, index) =>
        // unary functions
        assert(e.args().length == 1)
        val fnDomain = convertFunctionDomain(e.args().head)
        assert(fnDomain == Real, "Unary function should have domain Real")
        Function(name, index, fnDomain, Real)
    }
  }

  /** Converts a nested list of arguments into nested tuples of reals */
  private def convertFunctionDomain(arg: MExpr): Sort = {
    if (arg.listQ()) {
      assert(arg.args().length == 2)
      Tuple(convertFunctionDomain(arg.args()(0)), convertFunctionDomain(arg.args()(1)))
    } else {
      Real
    }
  }

  def unmaskName(e: MExpr): (String, Option[Int]) = {
    val maskedName = e.asString().replaceAll(regexOf(MUNDERSCORE), "_")
    //@todo Code Review: contains --> startsWith, improve readability/prefix+sep handling in a single name
    if (maskedName.contains(PREFIX) && maskedName.contains(SEP)) {
      //Get the parts of the masked name.
      val parts = maskedName.replace(PREFIX, "").split(regexOf(SEP))
      if (parts.size != 2) throw new ConversionException("Expected " + SEP + " once only.")
      val (name, unparsedIndex) = (parts.head, parts.last)

      val index = try {
        Integer.parseInt(unparsedIndex)
      } catch {
        case e : NumberFormatException => throw new ConversionException("Expected number for index")
      }
      (name, Some(index))
    }
    else if (maskedName.contains(PREFIX) && !maskedName.contains(SEP)) {
      (maskedName.replace(PREFIX, ""), None)
    } else {
      (maskedName, None)
    }
  }
}

