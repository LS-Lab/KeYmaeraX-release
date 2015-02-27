package edu.cmu.cs.ls.keymaera.tacticsinterface

import edu.cmu.cs.ls.keymaera.core.{ProofNode, Position}
import edu.cmu.cs.ls.keymaera.tactics.{Tactics, TacticLibrary, SearchTacticsImpl}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{LabelBranch, Tactic, PositionTactic}

/**
 * *C*ombinator *L*anguage *T*erms
 * Created by nfulton on 2/26/15.
 */
abstract class CLTerm
  case class WeakSeqC(left : CLTerm, right : CLTerm)   extends CLTerm
  case class StrongSeqC(left : CLTerm,
                        right : List[CLTerm])          extends CLTerm
  case class SeqC(left : CLTerm, right : CLTerm)       extends CLTerm
  case class OrC(left : CLTerm, right : CLTerm)        extends CLTerm
  case class BranchC(children : List[CLTerm])          extends CLTerm
  case class KleeneC(child : CLTerm)                   extends CLTerm
  case class LabelC(name : String)                     extends CLTerm
  case class OnLabelC(label : String, term : CLTerm)   extends CLTerm //@todo add support for the more typical onBranch((), (), ...)
  case class BuiltInC(name : String)                   extends CLTerm
  case class PosApplyC(name : String, pos : Position)  extends CLTerm //punting the problem of representing and mapping positions to the grammar/parser.
//  case class ifC(cond : _, term : CLTerm)              extends CLTerm //Decided to delay support; see Andre/Stefan/Nathan email 26/2.

/**
 * The *C*ombinator *L*anguage *Interpreter*
 * A reflective interpreter for the tactic combinator language.
 */
object CLInterpreter {
  class BuiltInTacticNotFoundEx(name : String) extends Exception("Did not find built-in ExposedTacticsLibrary."+name)
  class InvalidTacticType(name : String, typeName : String) extends Exception("Did not find a Tactic or PositionTactic return type for the method ExposedTacticsLibrary."+name + " (expected Tactic or PositionTactic, but found "+typeName)
  class CombinatorTypeError(msg : String) extends Exception("Found a 'type error' in your tactic: " + msg)

  /**
   * All "built-in" tactics should be explicitly included in the ExposedTacticsLibrary.
   * @param name The name of a method in ExposedTacticLibrary
   * @todo security audit
   * @return The tactic.
   */
  def getBuiltIn(name : String) : Either[Tactic, PositionTactic] =
    ExposedTacticsLibrary.getClass().getMethods().find(_.getName().equals(name)) match {
      case Some(method) => {
        val ru = scala.reflect.runtime.universe; //The *r*untime *u*niverse.
        //The symbol corresponding to the requested method.
        val methodSymbol : ru.MethodSymbol = ru.typeOf[ExposedTacticsLibrary.type].declaration(ru.newTermName(name)).asMethod

        //See http://bracha.org/mirrors.pdf and the Scala reflection documentation.
        val instanceMirror = ru.runtimeMirror(getClass.getClassLoader()).reflect(ExposedTacticsLibrary)
        val methodMirror   = instanceMirror.reflectMethod(methodSymbol)

        //construct a wrapper so that we return a function instead of a mirror.
        val returnTypeName = method.getReturnType().getSimpleName()

        if(returnTypeName.equals("Tactic")) {
          Left(methodMirror().asInstanceOf[Tactic])
        }
        else if(returnTypeName.equals("PositionTactic")) {
          Right(methodMirror().asInstanceOf[PositionTactic])
        }
        else {
          throw new InvalidTacticType(name, returnTypeName)
        }
      }
      case None => throw new BuiltInTacticNotFoundEx(name)
    }

  /**
   *
   * @param tactic
   * @return A tactic corresponding to the CLTerm ``tactic"
   */
  def construct(tactic : CLTerm) : Tactic = tactic match {
    case WeakSeqC(left,right) => construct(left) ~ construct(right)
    case StrongSeqC(left,right:List[CLTerm]) => {
      val l = construct(left)
      val rs = right.map(construct(_))
      l && rs
    }
    case SeqC(left,right) => construct(left) & construct(right)
    case OrC(left,right) => construct(left) | construct(right)
    case BranchC(children) => ???
    case KleeneC(child) => (construct(child) *)
    case LabelC(label) => LabelBranch(label)
    case OnLabelC(label, term) => SearchTacticsImpl.onBranch(label, construct(term))
    case PosApplyC(name, pos) => {
      val tactic = getBuiltIn(name)
      if(tactic.isRight) (tactic.right.get)(pos)
      else throw new CombinatorTypeError("Cannot apply a built-in, non-position tactic to a position.")
    }
    case BuiltInC(name : String) => {
      val tactic = getBuiltIn(name)
      //Can't pattern match because tactic maps out to LCA(Tactic, PositionTactic) = Object.
      if(tactic.isLeft) tactic.left.get
      else throw new CombinatorTypeError("Cannot use a built-in position tactic without specifying a position")
    }
  }

  /**
   * Constructs a tactic corresponding to term and runs it on the node using runner.
   * @param term
   * @param node
   */
  def apply(term : CLTerm, node : ProofNode) = ??? //@todo punting this into hydra for now, b/c it's not clear how to schedule from here.
}

