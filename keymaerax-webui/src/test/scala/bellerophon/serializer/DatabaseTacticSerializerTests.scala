package edu.cmu.cs.ls.keymaerax.bellerophon.serializer

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{Idioms, ProofRuleTactics, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.{AntePos, Formula, Provable, SuccPos}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.hydra.{DatabaseTacticSerializer, SQLite}
import org.scalatest.{FlatSpec, Matchers}


/**
  * Created by nfulton on 12/22/15.
  */
class DatabaseTacticSerializerTests extends FlatSpec with Matchers {
  "serializer" should "print something we thing we can serialize and deserialize for input and dependent position tactics" in {
    val serializer = new DatabaseTacticSerializer(SQLite.TestDB)
    val interpreter = SequentialInterpreter(Seq(serializer))

    val input = BelleProvable(Provable.startProof("1=1".asFormula))
    val tactic = new InputTactic[Formula]("TestInputTactic", "1=1".asFormula) {
      override def computeExpr(): BelleExpr = PartialTactic(Idioms.nil)
    }

    //@todo so what is the test?
    interpreter(tactic, input)
  }

}
