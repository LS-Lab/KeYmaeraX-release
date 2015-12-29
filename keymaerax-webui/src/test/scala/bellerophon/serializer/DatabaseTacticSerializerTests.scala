package bellerophon.serializer

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics
import edu.cmu.cs.ls.keymaerax.core.{SuccPos, AntePos, Provable}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.hydra.{DatabaseTacticSerializer, SQLite}
import org.scalatest.{Matchers, FlatSpec}


/**
  * Created by nfulton on 12/22/15.
  */
class DatabaseTacticSerializerTests extends FlatSpec with Matchers {
  "serializer" should "print something we thing we can serialize and deserialize for input and dependent position tactics" in {
    val serializer = new DatabaseTacticSerializer(SQLite.TestDB)
    val interpreter = new SequentialInterpreter(Seq(serializer))

    val input = BelleProvable(Provable.startProof("1=1".asFormula))
    val tactic = ProofRuleTactics.cutR("1=1".asFormula)(SuccPos(0)) partial

    interpreter(tactic, input)
  }

}
