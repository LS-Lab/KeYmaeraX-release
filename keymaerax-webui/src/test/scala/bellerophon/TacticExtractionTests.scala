package bellerophon

import edu.cmu.cs.ls.keymaerax.hydra.{ExtractTacticFromTrace, SQLite}
import org.scalatest.{FlatSpec, Matchers}

/**
  * Created by nfulton on 1/12/16.
  */
class TacticExtractionTests extends FlatSpec with Matchers {
  "extractor" should "extract a proof from the SQLite default database" in {
    println(new ExtractTacticFromTrace(SQLite.ProdDB).apply(12))
  }
}
