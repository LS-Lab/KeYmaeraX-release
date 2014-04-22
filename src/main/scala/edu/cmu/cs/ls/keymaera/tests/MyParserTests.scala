package edu.cmu.cs.ls.keymaera.tests

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import scala.swing.FileChooser
import java.io.File
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import javax.swing.JOptionPane

object MyParserTests {
  def main(args:Array[String]):Unit = {
    //TODO-nrf make these equivalence checks.
    val tests = 
      "[x := 1] x = 1" ::
      "[x := 1] x = 1 -> [x := 2] x = 2" ::
      "[x := 1] x = 1 & [x := 2] x = 2" ::
      "[x := 1] x = 1 | [x := 2] x = 2" ::
      Nil

    val p = new KeYmaeraParser()
 
    tests.map(formula => {
      val test = "ProgramVariables.\n" + "R x. R y. R z." + "\nEnd." +
        "Problem.\n" + formula + "\nEnd."
      val result = p.runParser(test)
      println(KeYmaeraPrettyPrinter.stringify(result))
      formula
    })
  
  }
}
