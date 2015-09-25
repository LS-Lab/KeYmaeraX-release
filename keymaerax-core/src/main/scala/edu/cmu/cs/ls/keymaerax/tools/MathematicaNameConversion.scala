/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tools

// favoring immutable Seqs
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.core._
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
  private val PREFIX = "KeYmaera`"
  private val SEP    = "$beginIndex$"
  private val MUNDERSCORE = "$underscore$" //Mathematica Underscore

  val CONST_FN_PREFIX: String = "constfn$"

  private def regexOf(s: String) = {
    s.replace("$", "\\$")
  }

  private def maskIdentifier(name : String) = {
    //Ensure that none of the "special" strings occur in the variable name.
    if (name.contains(MUNDERSCORE)) {
      throw new ConversionException("Please do not use the string " + MUNDERSCORE + " in your variable names.")
    }
    //Do replacements.
    name.replace("_", MUNDERSCORE)
  }


  def toMathematica(ns : NamedSymbol) : com.wolfram.jlink.Expr = {
    //The identifier (portion of name excluding index) has one of the forms:
    //   name (for external functions)
    //   KeYmaera + name
    val identifier : String = ns match {
      //@note special function
      case Function("abs",None,Real,Real) => "Abs"
      case Function("Abs",None,Real,Real) => throw new IllegalArgumentException("Refuse translating Abs to Mathematica to avoid confusion with abs")
      case Function("min",None,Tuple(Real,Real),Real) => "Min"
      case Function("Min",None,Tuple(Real,Real),Real) => throw new IllegalArgumentException("Refuse translating Min to Mathematica to avoid confusion with min")
      case Function("max",None,Tuple(Real,Real),Real) => "Max"
      case Function("Max",None,Tuple(Real,Real),Real) => throw new IllegalArgumentException("Refuse translating Max to Mathematica to avoid confusion with max")
      //      case n: Function if n.external => n.name
      case _ => PREFIX + maskIdentifier(ns.name)
    }

    //Add the index if it exists.
    val fullName : String   = ns.index match {
      case Some(idx) => identifier + SEP + idx.toString
      case None      => identifier
    }
    new com.wolfram.jlink.Expr(com.wolfram.jlink.Expr.SYMBOL, fullName)
  } ensuring (r => r.symbolQ(), "symbol names expected as result")

  ////
  // toKeYmaera section. We decompose by function vs. variable. In each case, we
  // decompose based upon the possible forms of the name:
  // PREFIX + base + SEP + index ---> name + index
  // PREFIX + base               ---> name only
  // base                        ---> external function
  ///
  def toKeYmaera(e: com.wolfram.jlink.Expr): NamedSymbol = {
    if (e.args().isEmpty) nullaryNameToKeYmaera(e)
    else functionToKeYmaera(e)
  }

  private def unmaskName(e: com.wolfram.jlink.Expr): (String, Option[Int]) = {
    val maskedName = e.asString().replaceAll(regexOf(MUNDERSCORE), "_")
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

  /** Returns a variable or function, depending on the prefix of the name */
  private def nullaryNameToKeYmaera(e: com.wolfram.jlink.Expr): NamedSymbol = {
    require(e.args().isEmpty, "Nullary names have no arguments")
    val (name, index) = unmaskName(e)
    if (name.startsWith(MathematicaNameConversion.CONST_FN_PREFIX)) Function(name.replace(CONST_FN_PREFIX, ""), index, Unit, Real)
    else Variable(name, index, Real)
  }

  private def functionToKeYmaera(e : com.wolfram.jlink.Expr) : NamedSymbol = {
    val (name, index) = unmaskName(e.head())
    require(!name.startsWith(MathematicaNameConversion.CONST_FN_PREFIX), "Proper functions are not constant functions")
    name match {
      //@note special function
      case "Abs" => Function("abs", None, Real, Real)
      case "Min" => Function("min", None, Tuple(Real, Real), Real)
      case "Max" => Function("max", None, Tuple(Real, Real), Real)
      //@note This conversion only works for real-valued unary functions not for others. Term creation will catch binary argument attempts.
      case _ => Function(name, index, Real, Real)
    }
  }
}

