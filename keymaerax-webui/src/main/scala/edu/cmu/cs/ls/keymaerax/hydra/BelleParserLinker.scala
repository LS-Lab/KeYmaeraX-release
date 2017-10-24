/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.{MathematicaToolProvider, ToolProvider}
/**
  * A very hacky way of parsing assignment notation in Bellerophon.
  *
  *
  * prfOne :==
  *   blah;
  *   blah
  *
  * main :=
  *   blah <(prfOne, prfOne)
  *
  * Again, VERY hacky. Recursive defs will inf loop. Doesn't print well. etc.
  *
  * @author Nathan Fulton
  */
object BelleParserLinker {
  def instantiator(definitions : List[(String,String)]) = definitions.map(definition => {
    val name = definition._1
    val tactic = definitions.foldLeft(definition._2)((newTactic, nextDefinition) => {
      newTactic.replaceAll(nextDefinition._1, nextDefinition._2) //@todo need delimiters for names to avoid replacing half-tactics...
    })
    (name, tactic)
  })

  def exhaustiveApplier(definitions : List[(String,String)]): List[(String,String)] = {
    val newDefs = instantiator(definitions);
    if(definitions.find(d => !newDefs.contains(d)).nonEmpty)
      exhaustiveApplier(newDefs)
    else
      newDefs
  }

  def apply(s1: String, mainTacticName: String = "main") = {
    //Remove comment lines. Note: all comments must be a single line!
    val s = s1.split("\n")
      .filter(p => !p.startsWith("/*"))
      .filter(p => !p.matches("^\\ *//.*"))
      .reduce(_ + "\n" + _)

    //Split up the definitions.
    val definitions = s.split("\n\n").filter(_.contains(":==")).map(definition => {
      val parts = definition.split(":==")
      assert(parts.length == 2, println(definition))
      (parts(0).replaceAll(" ","").replaceAll("\n",""), parts(1))
    }).toList

    val instantiatedDefinitions = exhaustiveApplier(definitions)


    instantiatedDefinitions.find(definition => definition._1 == mainTacticName) match {
      case Some(main) => {
        val result = main._2.replaceAll("`exists","`\\\\exists")
        BelleParser(result) //will result in exn if not parsed
        result
      }
      case None => throw new Exception(s"Did not find a tactic named '${mainTacticName}'")
    }
  }
}

object BelleParserMain {
  def main(args: Array[String]) = {
    val s = scala.io.Source.fromFile("/home/nfulton/dev/scuba/time_triggered_better_hr/padi/below_lactate_threshold/proof.kyt").getLines().mkString("\n")
    ToolProvider.setProvider(new MathematicaToolProvider(HyDRAInitializer.mathematicaConfigFromDB(DBAbstractionObj.defaultDatabase)))
    println(BelleParserLinker(s, "main"))
  }
}
