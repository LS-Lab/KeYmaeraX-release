package bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.hydra.{ExtractTacticFromTrace, SQLite}
import org.scalatest.{FlatSpec, Matchers}

/**
  * Created by nfulton on 1/12/16.
  */
class TacticExtractionTests extends TacticTestBase {
  "extractor" should "extract a proof from the SQLite default database" in withMathematica { implicit qeTool => {
    println(new ExtractTacticFromTrace(SQLite.ProdDB).apply(10))
  }}
}
