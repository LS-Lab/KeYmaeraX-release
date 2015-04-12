package testHelper

import java.io.File

import edu.cmu.cs.ls.keymaera.api.ComponentConfig
import edu.cmu.cs.ls.keymaera.core.{Sequent, Formula}
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser

/**
 * Created by ran on 2/4/15.
 * @author Ran Ji
 */
object ParserFactory {

  /**
   * return the sequent from a .key file
   * @param file
   * @return
   */
  def parseToSequent(file : File) = {
    val content = io.Source.fromFile(file).mkString
    new KeYmaeraParser(false, ComponentConfig).runParser(content) match {
      case f: Formula => Sequent(List(), collection.immutable.IndexedSeq[Formula](), collection.immutable.IndexedSeq[Formula](f))
      case a => throw new IllegalArgumentException("Parsing the input did not result in a formula but in: " + a)
    }
  }

  /**
   * return the formula from a .key file
   * @param file
   * @return
   */
  def parseToFormula(file : File) = {
    val content = io.Source.fromFile(file).mkString
    new KeYmaeraParser(false, ComponentConfig).runParser(content) match {
      case f: Formula => f
      case a => throw new IllegalArgumentException("Parsing the input did not result in a formula but in: " + a)
    }
  }
}
