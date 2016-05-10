import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._

import scala.language.postfixOps

/**
  * A script tactic gives you full control over the proof. In most cases, searchier tactics are less painful to write
  * and less fragile to model changes.
  * @see [[CheatSheetSearchyTactic]]
  */
class CheatSheetScriptTactic extends (() => BelleExpr) {

  def apply() = {
    /* Proof script, follows the structure of the problem in CheatSheet.kyx */

    /* loop invariant as a String, long invariants can use Scala '|'-delimited multi-line strings for readability */
    val invariant: Formula =
      """
        |
        | v>=0
        |
      """.stripMargin.asFormula     /* asFormula parses the String into a formula */

    /* Most tactics need positions: negative values -1,... point to the antecedent, positive values 1,... to the succedent */

    /* A subtactic for proving the induction step, will be used in the overall tactic below */
    val inductionStepTactic: BelleExpr = (
        composeb(1)            /* turn sequential composition [a;b]p into [a][b]p */
      & choiceb(1)             /* turn nondeterministic choice [a++(b++c)]p into [a]p & [b++c]p */
      & choiceb(1, 1::Nil)     /* point to second conjunct inside formula: turn nondeterministic choice [a]p & [b++c]p into [a]p & [b]p & [c]p */
      /* work on acceleration ?v<=5;a:=A; */
      & composeb(1, 0::Nil)     /* point to first conjunct: turn [?q;a:=A;]p & [c]p into [?q][a:=A;]p & [c]p */
      & assignb(1, 0::1::Nil)   /* point to second box in first conjunct: turn [?q][a:=A;]p(a) into [?q]p(A) */
      & testb(1, 0::Nil)        /* turn [?q]p(A) into q->p(A) */
      /* work on coasting a:=0 */
      & assignb(1, 1::0::Nil)   /* point to first conjunct in second conjunct, a.k.a. b in a & b & c */
      /* work on braking */
      & assignb(1, 1::1::Nil)   /* point to second conjunct in second conjunct, a.k.a. c in a & b & c */
      & andR(1) <(              /* now split the conjunction, because diffSolve only works top-level */
        implyR(1) & diffSolve()(1) & QE
        ,
        andR(1) <(
          diffSolve()(1) & QE
          ,
          diffSolve()(1) & QE
          )
        )
      )

    /* Creates the actual tactic */
    val tactic: BelleExpr = (
        implyR(1)                      /* apply implyR to first formula in succedent */
                                       /* implyR('R) == first -> in succedent */
                                       /* implyR('_) == first -> in either antecedent or succedent where implyR is applicable */
      &                                /* tactic combinator a & b: first do 'a' then do 'b' on the result of 'a'; both must succeed */
        andL('L)*@TheType()            /* tactic a*: exhaustively apply a */
      & loop(invariant)(1) <(          /* tactic a<(b,c): expects 'a' to produce 2 subgoals, does 'b' on subgoal 1 and 'c' on subgoal 2 */
        print("Base case") & QE        /* print to the console and close real arithmetic goal */
        ,
        print("Use case") & QE
        ,
        print("Induction step") & inductionStepTactic     /* call a subtactic defined earlier in this file */
      )
    )

    tactic
  }
}
