package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.btactics.{AxiomInfo, DerivedAxiomInfo, DerivedRuleInfo, ProvableInfo}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{US, _}

import scala.collection.immutable

/**
 * ProofChecker maps a proof term to the Provable it proves.
 * {{{
 *   ProofChecker : ProofTerm * Formula => Provable
 * }}}
 * with a successful answer if the proof indeed checked successfully.
 * Not soundness-critical, because the proof checker compiles the proof term into
 * subsequent proof rule and axiom applications in the [[edu.cmu.cs.ls.keymaerax.core prover core]].
 * Created by nfulton on 10/15/15.
  *
  * @author Nathan Fulton
  * @author Brandon Bohrer
 * @see [[ProofTerm]]
 * @see [[ProvableSig]]
 */
object ProofChecker {
  case class ProofCheckException(str: String) extends Exception {}

  private val tool = new edu.cmu.cs.ls.keymaerax.tools.Mathematica()

  private def goalSequent(phi : Formula) = Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(phi))
  private def proofNode(phi : Formula) = ProvableSig.startProof(goalSequent(phi))
  private def proofNode(phi : Sequent) = ProvableSig.startProof(phi)

  /**
   * Converts proof term e for goal phi into a Provable iff e indeed justifies phi.
    *
    * @todo could remove phi except no more contract then
   */
  def apply(e: ProofTerm, phi: Option[Formula] = None) : ProvableSig = {
    val result : ProvableSig =
      e match {
        case FOLRConstant(f) => {
          val node = proofNode(f)
          proveBy(node, QE & done)
        }

        case AxiomTerm(axiomName) => {
          try {
            val info = ProvableInfo.ofStoredName(axiomName)
            val axiomFml = info.provable.conclusion
            val node = proofNode(axiomFml)
            //@TODO: Why?
            //Just do an empty uniform substitution...
            proveBy(node, US(USubst.apply(scala.collection.immutable.Seq()), info.canonicalName))
          } catch {
            // If derived axioms didn't do it, try core axioms too
            case e:Exception =>
              val axiomFml = AxiomInfo(axiomName).provable.conclusion
              val node = proofNode(axiomFml)
              proveBy(node, US(USubst.apply(scala.collection.immutable.Seq()), axiomName))
          }
        }

        case RuleApplication(child, ruleName, subgoal, sequentPositions, expArgs) =>
          val ps:ProvableSig = apply(child)
          def pos(i:Int):SeqPos = sequentPositions(i)
          def apos(i:Int):AntePos = sequentPositions(i).asInstanceOf[AntePos]
          def spos(i:Int):SuccPos = sequentPositions(i).asInstanceOf[SuccPos]
          def f(i:Int):Formula = expArgs(i).asInstanceOf[Formula]
          def v(i:Int):Variable = expArgs(i).asInstanceOf[Variable]
          def pr(r:Rule):ProvableSig = ps(r, subgoal)
          ruleName match {
            case "Close" => pr(Close(apos(0),spos(1)))
            case "CoHide2"  => pr(CoHide2(apos(0),spos(1)))
            case "cut Right" => pr(CutRight(f(0),spos(0)))
            case "Imply Right"=> pr(ImplyRight(spos(0)))
            case "And Right"=> pr(AndRight(spos(0)))
            case "CoHideRight" => pr(CoHideRight(spos(0)))
            case "CommuteEquivRight" => pr(CommuteEquivRight(spos(0)))
            case "EquivifyRight" => pr(EquivifyRight(spos(0)))
            case "Equiv Right" => pr(EquivRight(spos(0)))
            case "Not Right" => pr(NotRight(spos(0)))
            case "CloseTrue" => pr(CloseTrue(spos(0)))
            case "HideRight" => pr(HideRight(spos(0)))
            case "Or Right"=> pr(OrRight(spos(0)))

            case "Or Left" => pr(OrLeft(apos(0)))
            case "And Left" => pr(AndLeft(apos(0)))
            case "HideLeft" => pr(HideLeft(apos(0)))
            case "cut Left" => pr(CutLeft(f(0),apos(0)))
            case "Imply Left"=> pr(ImplyLeft(apos(0)))
            case "Not Left" => pr(NotLeft(apos(0)))
            case "Equiv Left" => pr(EquivLeft(apos(0)))
            case "CloseFalse" => pr(CloseFalse(apos(0)))

            case "Bound Renaming" => pr(BoundRenaming(v(0),v(1),pos(0)))
            case "Uniform Renaming" => pr(UniformRenaming(v(0),v(1)))
            case "Skolemize" => pr(Skolemize(pos(0)))
            case "cut" => pr(Cut(f(0)))

            case name => throw ProofCheckException("Unsupported rule \"" + name + "\" found during proof replay")
          }

        case RuleTerm(name) =>
          if(ProvableSig.rules.contains(name))
            ProvableSig.rules(name)
         else
            DerivedRuleInfo.allInfo.find(info => info.storedName == name).get.provable

        case ForwardNewConsequenceTerm(child, con, rule) =>
          val pschild = apply(child)
          pschild(con,rule)

        case ProlongationTerm(child, pro) =>
          val pschild = apply(child)
          val pspro = apply(pro)
          pschild(pspro)

        case Sub(child,sub,i) =>
          val pschild = apply(child)
          val pssub = apply(sub)
          pschild(pssub,i)

        case StartProof(goal) => ProvableSig.startProof(goal)

        case NoProof() => throw ProofCheckException("Tried to check proof of " + phi + ", but it has NoProof()")

        case UsubstProvableTerm(child, sub) =>
          val pschild = apply(child)
          pschild(sub)
      }

    result
  } ensuring(r => phi.isEmpty || r.conclusion == goalSequent(phi.get), "Resulting Provable proves given formula if defined for " + phi + " : " + e)
}
