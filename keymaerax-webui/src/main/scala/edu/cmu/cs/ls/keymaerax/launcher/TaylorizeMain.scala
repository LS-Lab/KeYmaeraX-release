/*
 * Copyright (c) 2021 MIT-IBM Watson AI Lab, IBM Research.
 */

package edu.cmu.cs.ls.keymaerax.launcher

import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core.{DifferentialProgram, ODESystem, PrettyPrinter, Term, Variable}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._


/**
  * The main class of Taylorizing sutff from the outside.
  *
  * @autor Nathan Fulton
  */
object TaylorizeMain {
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)

  def apply(fileName: String) = parseFile(fileName) match {
    case Some(dp) => taylorize(dp) match {
      case Some(listOfBounds) => listOfBounds.map(bounds => output(bounds._1, bounds._2, bounds._3)).reduce(_ + _)
      case None => s"FAILED.\nKeYmaera X does not know how to construct a Taylor approximation of the system ${dp.prettyString}"
    }
    case None => s"FAILED.\nKeYmaera X does not know how to parse file ${fileName} with contents ${scala.io.Source.fromFile(fileName).mkString} into a DifferentialProgram."
  }

  def parseFile(fileName: String): Option[DifferentialProgram] = {
    try {
      val fileContents = scala.io.Source.fromFile(fileName).mkString
      try {
        Some(fileContents.asDifferentialProgram)
      } catch {
        case pe: edu.cmu.cs.ls.keymaerax.parser.ParseException => try {
          Some(fileContents.asProgram.asInstanceOf[ODESystem].ode)
        } catch {
          case _: Throwable => None
        }
        case _: Throwable => None
      }
    }
    catch {
      case e: java.io.FileNotFoundException => None
    }
  }

  def taylorize(dp: DifferentialProgram): Option[List[(Variable, Term, Term)]] = {
    val vars = DifferentialHelper.atomicOdes(dp).map(atomic => atomic.xp.x)

    //@todo Grab the taylor approximations from KeYmaera X backend FOR EACH PRIMED VARIABLE.
    //@todo This whole section is complete nonsesnse filler.

    Some(vars.map((v: Variable) => {
      val name = v.name
      (v, s"t^2/2".asTerm, s"t^3/3".asTerm)
    }))
  }

  def output(v: Variable, lowerBound: Term, upperBound: Term) = {
    s"\nvariablename:${v}\nlowerbound:${lowerBound.prettyString}\nupperbound:${upperBound.prettyString}\n"
  }
}
