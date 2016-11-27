package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core.{PrettyPrinter, Sequent}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import scala.collection.immutable.IndexedSeq
import org.scalatest.{Matchers, FlatSpec}
import edu.cmu.cs.ls.keymaerax.btactics.DLBySubst
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * Created by nfulton on 11/3/15.
  */
class demo extends FlatSpec with Matchers {
  val listener = new IOListener() {
    override def begin(input: BelleValue, expr: BelleExpr) : Unit = {
      println(expr.getClass)
    }
    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, BelleError]): Unit= {
    }
    override def kill():Unit = ()

  }

  val interp = SequentialInterpreter(Seq(listener))

  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)

  "usubst style dL tactic" should "work" in {
    val s = Sequent(IndexedSeq("[x:=1;]x>0".asFormula), IndexedSeq("[x:=1;]x>0".asFormula))
    val output = interp(TactixLibrary.monb, BelleProvable(ProvableSig.startProof(s)))
    output match {
      case BelleProvable(p, _) => println(p.prettyString)
    }
  }
}
