package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.core.{PrettyPrinter, Provable, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import scala.collection.immutable.IndexedSeq
import org.scalatest.{Matchers, FlatSpec}
import edu.cmu.cs.ls.keymaerax.btactics.DLBySubst
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * Created by nfulton on 11/3/15.
  */
class demo extends FlatSpec with Matchers {
  val interp = SequentialInterpreter()

  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)

  "usubst style dL tactic" should "work" in {
    val s = Sequent(Nil, IndexedSeq("[x:=1;]x>0".asFormula), IndexedSeq("[x:=1;]x>0".asFormula))
    val output = interp(DLBySubst.monb, BelleProvable(Provable.startProof(s)))
    output match {
      case BelleProvable(p) => println(p.prettyString)
    }
  }
}
