package testHelper

import edu.cmu.cs.ls.keymaerax.api.ComponentConfig
import edu.cmu.cs.ls.keymaerax.core.{Sequent, Formula}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXProblemParser, ProblemFileMode, KeYmaeraXParser, KeYmaeraParser}

/**
 * Created by ran on 2/4/15.
 * @author Ran Ji
 * @author Stefan Mitsch
 * @todo adapt to new KeYmaeraXParser
 */
object ParserFactory {

  /**
   * Returns the sequent from an input stream.
   * @param in The input stream.
   * @return The sequent.
   */
  def parseToSequent(in: java.io.InputStream) = {
    val content = io.Source.fromInputStream(in).mkString
    KeYmaeraXProblemParser(content) match {
      case f: Formula => Sequent(List(), collection.immutable.IndexedSeq[Formula](), collection.immutable.IndexedSeq[Formula](f))
      case a => throw new IllegalArgumentException("Parsing the input did not result in a formula but in: " + a)
    }
  }
}
