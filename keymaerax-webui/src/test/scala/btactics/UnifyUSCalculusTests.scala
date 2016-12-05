package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, PosInExpr, RenUSubst, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.UnifyUSCalculus
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

/**
  * Created by yongkiat on 12/5/16.
  *
  * Documents some failures in UnifyUSCalculus, and usage of a few primitives
  *
  */
class UnifyUSCalculusTests extends TacticTestBase {

  //Unifier manages to unify F_() - F_() with bad LHS
  "UnifyUSCalculus" should "unify weirdly" ignore withMathematica { qeTool =>
    val minusCancel = proveBy("F_() - F_() = 0".asFormula,TactixLibrary.QE)
    val minusReflex = proveBy("A_() - B_() = -B_() + A_()".asFormula,TactixLibrary.QE)
    val fml = "x - y = z".asFormula
    //Both of the following fail because of unification
    proveBy(fml,useAt("ANON", minusCancel,PosInExpr(0::Nil))(SuccPosition(1, 0 :: Nil)))
    useFor(minusCancel, PosInExpr(0 :: Nil))(SuccPosition(1, 0 :: Nil))(minusReflex)
  }

  //Various kinds of CEating
  "UnifyUSCalculus" should "rewrite implications" in withMathematica { qeTool =>
    val impl = proveBy(" F_()^2 = 0 -> F_() = 0 ".asFormula,QE)
    val impl2 = proveBy(" F_() = 0 -> F_()^2 = 0 ".asFormula,QE)
    val impl3 = proveBy(" F_()^2 = 0 <-> F_() = 0 ".asFormula,QE)
    val impl4 = proveBy(" Q_()^2 = 0 <-> Q_() = 0 ".asFormula,QE)
    val impl5 = proveBy(" Q_() = 0 -> Q_()^2 = 0 ".asFormula,QE)
    val impl6 = proveBy(" Q_()^2 = 0 -> Q_() = 0 ".asFormula,QE)

    val (ctx1,_) = Context.at("Q_() = 0 -> F_() = 0".asFormula,PosInExpr(1::Nil))
    val (ctx2,_) = Context.at("Q_() = 0 -> F_()^2 = 0".asFormula,PosInExpr(0::Nil))
    println(ctx1,ctx2)
    val antes = IndexedSeq("F_()=0".asFormula,"F_()=0".asFormula,"Q_() = 0 -> F_()=0".asFormula,"Q_()=0 -> F_() = 0".asFormula)
    val succs = antes

    val pr = proveBy(Sequent(antes,succs),
      //The position passed in identifies the location of the key to match in rewritten position

      //Succedent rewrite
      DebuggingTactics.print("Initial") &
      useAt("ANON",impl,PosInExpr(1::Nil))(2) & //F_() is matched and strengthened to F_()^2 using F^2=0 -> F =0
      //Antecedent rewrite
      useAt("ANON",impl2,PosInExpr(0::Nil))(-2) & //F_() is matched and weakened to F_()^2 using F=0 -> F^2=0
      DebuggingTactics.print("After useAt") &

      //Same as above, except now just giving it straight to CEat
      //Default behavior: equivalences and equalities L <-> R are rewritten R to L
      CEat(impl3,ctx1)(3) & //Equiv CEat in positive position
      CEat(impl4,ctx2)(3) & //Equiv CEat in negative position
      DebuggingTactics.print("After <-> CEats") &

      //Implications need to be more careful

      CEat(impl)(1) & //Succedent top level rewrites in the usual right to left order
      CEat(impl2)(-1) & //Antecedent top level rewrites LEFT TO RIGHT i.e. A |- C rewritten with A -> B gives B |- C
      DebuggingTactics.print("After -> top level CEats")  &

      //CEating in a positive succedent position (A -> B rewritting B using C -> B gives A -> C)
      CEat(impl)(SuccPosition(4, 1 :: Nil)) &
      //CEating in a NEGATIVE succedent position (A -> B rewritting A using A -> C gives C -> B)
      CEat(impl5)(SuccPosition(4, 0 :: Nil)) &

      DebuggingTactics.print("After succedent non-toplevel CEats")  &

      //CEating in a positive antecedent position ~= negative succedent position
      CEat(impl2)(AntePosition(4, 1 :: Nil)) & // A -> B |- C rewritten with B ->D gives A -> D |- C
      CEat(impl6)(AntePosition(4, 0 :: Nil)) & // A -> B |- C rewritten with D -> A gives D -> B |- C

      DebuggingTactics.print("After antecedent non-toplevel CEats")  &

      //CEating with contexts
      nil //CEat(impl,ctx)
    )
//      & useAt("ANON",impl,PosInExpr(1::Nil))(-1))

  }

}
