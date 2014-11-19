package edu.cmu.cs.ls.keymaera.api

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import scala.Left
import edu.cmu.cs.ls.keymaera.parser.{ParseSymbols, KeYmaeraPrettyPrinter}
import scala.collection.immutable.Seq
import edu.cmu.cs.ls.keymaera.core.Sequent
import scala.Some
import edu.cmu.cs.ls.keymaera.core.PosInExpr

/**
 * Created by jdq on 6/13/14.
 */
object JSONConverter {
  val prettyPrinter = new KeYmaeraPrettyPrinter(ParseSymbols) //todo use appropriate symbol table.

  def printPos(p: PosInExpr): Any =
    p.pos.mkString(",")

  def printNamedSymbol(n: NamedSymbol): String = "\"" + n.name + (n.index match { case Some(j) => "_" + j case _ => "" }) + "\""

  def printForm(formula: Formula, formulaId: String, nodeId: String): String = {
    var jsonResult: String = ""
    val fn = new ExpressionTraversalFunction {

      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        jsonResult += (e match {
          case True() => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\": \"true\"}"
          case False() => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\": \"false\"}"
          case x@PredicateConstant(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\": " + printNamedSymbol(x.asInstanceOf[PredicateConstant]) + "}"
          case ApplyPredicate(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"apply\", \"children\": [ " + printNamedSymbol(a) + ", "
          case Equals(d, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"equals\"" + ", \"children\": [ "
          case NotEquals(d, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"notEquals\"" + ", \"children\": [ "
          case ProgramEquals(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"programEquals\"" + ", \"children\": [ "
          case ProgramNotEquals(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"programNotEquals\"" + ", \"children\": [ "
          case LessThan(d, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"lt\"" + ", \"children\": [ "
          case LessEqual(d, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"leq\"" + ", \"children\": [ "
          case GreaterEqual(d, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"geq\"" + ", \"children\": [ "
          case GreaterThan(d, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"gt\"" + ", \"children\": [ "
          case Not(a) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"not\"" + ", \"children\": [ "
          case And(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"and\"" + ", \"children\": [ "
          case Or(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"or\"" + ", \"children\": [ "
          case Imply(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"imply\"" + ", \"children\": [ "
          case Equiv(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"equiv\"" + ", \"children\": [ "
          case BoxModality(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"boxmodality\"" + ", \"children\": [ "
          case DiamondModality(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"diamondmodality\"" + ", \"children\": [ "
          case Forall(v, a) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"forall\", \"variables\": [" + v.map(printNamedSymbol).mkString(",") + "], \"children\": [ "
          case Exists(v, a) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"exists\", \"variables\": [" + v.map(printNamedSymbol).mkString(",") + "], \"children\": [ "
          case _ => throw new UnsupportedOperationException("not implemented yet for " + prettyPrinter.stringify(e) + " type " + e.getClass)
        })
        Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        jsonResult += (e match {
          case Number(s, i) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"" + i + "\"}"
          case x@Variable(_, _, _) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":" + printNamedSymbol(x.asInstanceOf[Variable]) + "}"
          case Apply(a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"apply\", \"children\": [ " + printNamedSymbol(a) + ", "
          case Neg(_, a) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"neg\"" + ", \"children\": [ "
          case Derivative(_, a) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"derivative\"" + ", \"children\": [ "
          case Add(_, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"add\"" + ", \"children\": [ "
          case Subtract(_, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"subtract\"" + ", \"children\": [ "
          case Multiply(_, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"multiply\"" + ", \"children\": [ "
          case Divide(_, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"divide\"" + ", \"children\": [ "
          case Exp(_, a, b) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"exp\"" + ", \"children\": [ "
          case _ => throw new UnsupportedOperationException("not implemented yet for " + prettyPrinter.stringify(e) + " type " + e.getClass)
        })
        Left(None)
      }

      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
        jsonResult += (e match {
          case x@ProgramConstant(_, _) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":" + printNamedSymbol(x.asInstanceOf[ProgramConstant]) + "}"
          case Assign(_, _) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"Assign\"" + ", \"children\": [ "
          case NDetAssign(_) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"NDetAssign\"" + ", \"children\": [ "
          case Sequence(_, _) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"Sequence\"" + ", \"children\": [ "
          case Choice(_, _) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"Choice\"" + ", \"children\": [ "
          case Test(_) => "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"Test\"" + ", \"children\": [ "
          case Loop(_) => "{" + "\"nodeId\":\"" + nodeId + "\", " + "\"id\": \"" + printPos(p) + "\", \"name\":\"Loop\"" + ", \"children\": [ "
          case _ => throw new UnsupportedOperationException("not implemented yet for " + prettyPrinter.stringify(e) + " type " + e.getClass)
        })
        Left(None)
      }
      override def inF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        jsonResult += ", "
        Left(None)
      }

      override def inT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        jsonResult += ", "
        Left(None)
      }

      override def inP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
        jsonResult += ", "
        Left(None)
      }

      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        jsonResult += (e match {
          case ApplyPredicate(a, b) => "]}"
          case Equals(d, a, b) => "]}"
          case NotEquals(d, a, b) => "]}"
          case ProgramEquals(a, b) => "]}"
          case ProgramNotEquals(a, b) => "]}"
          case LessThan(d, a, b) => "]}"
          case LessEqual(d, a, b) => "]}"
          case GreaterEqual(d, a, b) => "]}"
          case GreaterThan(d, a, b) => "]}"
          case Not(a) => "]}"
          case And(a, b) => "]}"
          case Or(a, b) => "]}"
          case Imply(a, b) => "]}"
          case Equiv(a, b) => "]}"
          case Modality(a, b) => "]}"
          case Forall(v, a) => "]}"
          case Exists(v, a) => "]}"
          case _ => ""
        })
        Left(None)
      }

      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        jsonResult += (e match {
          case Apply(a, b) => "]}"
          case Neg(_, a) => "]}"
          case Derivative(_, a) => "]}"
          case Add(_, a, b) => "]}"
          case Subtract(_, a, b) => "]}"
          case Multiply(_, a, b) => "]}"
          case Divide(_, a, b) => "]}"
          case Exp(_, a, b) => "]}"
          case _ =>""
        })
        Left(None)
      }

      override def postP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
        jsonResult += (e match {
          case Assign(_) => "]}"
          case NDetAssign(_) => "]}"
          case Test(_) => "]}"
          case Loop(_) => "]}"
          case Sequence(_, _) => "]}"
          case Choice(_, _) => "]}"
          case _ =>""
        })
        Left(None)
      }
    }
    ExpressionTraversal.traverse(fn, formula)
    jsonResult
  }

  //def print(l: Seq[Formula]): String = (for(f <- l) yield KeYmaeraPrettyPrinter.stringify(f).replaceAll("\\\\", "\\\\\\\\")).mkString(",")
  def print(l: Seq[Formula], ante: String, nodeId: String): String = (for(f <- l.zipWithIndex) yield "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"id\":\"" + ante + ":" + f._2 + "\", \"formula\":" + printForm(f._1, ante + ":" + f._2, nodeId) + "}").mkString(",")
  def print(s: Sequent, nodeId: String): String = "{ " + "\"nodeId\":\"" + nodeId + "\", " + "\"ante\": [" + print(s.ante, "ante", nodeId) + "], \"succ\": [" + print(s.succ, "succ", nodeId) + "]}"
  def print(id: String, limit: Option[Int], store: ((ProofNode, String) => Unit))(p: ProofNode): String = {
    store(p, id)
    "{ \"id\":\"" + id + "\"," + sequent(p, id) + "," + infos(p) +
      "\"children\": [ " +
      (limit match {
        case Some(l) if l > 0 => p.children.zipWithIndex.map(ps => print(id, limit.map(i => i - 1), ps._1, ps._2, store)).mkString(",")
        case _ => ""}) + "]}"
  }
  def print(id: String, limit: Option[Int], ps: ProofStep, i: Int, store: ((ProofNode, String) => Unit)): String =
    "{\"rule\":\"" + ps.rule.toString + "\", " +
    "\"id\":\"" + i + "\", " +
    "\"children\": [" + subgoals(id, limit, store)(ps).mkString(",") + "]" + "}"

  def print(id: String, filter: (ProofStepInfo => Boolean), store: (ProofNode, String) => Unit)(p: ProofNode): String = {
    store(p, id)
    "{ " + sequent(p, id) + "," + infos(p) +
      "\"children\": [ " +
      p.children.zipWithIndex.filter(ps => filter(ps._1.tacticInfo)).map(ps => print(id, filter, ps._1, ps._2, store)).mkString(",")  + "]}"
  }

  def print(id: String, filter: (ProofStepInfo => Boolean), ps: ProofStep, i: Int, store: (ProofNode, String) => Unit): String =
    "{\"rule\":\"" + ps.rule.toString + "\", " +
    "\"id\":\"" + i + "\", " +
    "\"children\": [" + subgoals(id, filter, store)(ps).mkString(",") + "]" + "}"

  private def infos(p: ProofNode) = p.tacticInfo.infos.map(s => "\"info-" + s._1 + "\":" + "\"" + s._2 + "\"").mkString(", ") + (if(p.tacticInfo.infos.size > 0) ", " else "")
  private def sequent(p: ProofNode, nodeId: String) = "\"sequent\":" + print(p.sequent, nodeId)
  private def updateIndex(id: String, limit: Option[Int], store: (ProofNode, String) => Unit)(in: (ProofNode, Int)): String = print(id + "_" + in._2, limit, store)(in._1)
  private def updateIndex(id: String, filter: (ProofStepInfo => Boolean), store: (ProofNode, String) => Unit)(in: (ProofNode, Int)): String = print(id + "_" + in._2, filter, store)(in._1)
  private def subgoals(id: String, limit: Option[Int], store: (ProofNode, String) => Unit)(ps: ProofStep): Seq[String] = ps.subgoals.zipWithIndex.map(updateIndex(id, limit, store))
  private def subgoals(id: String, filter: (ProofStepInfo => Boolean), store: (ProofNode, String) => Unit)(ps: ProofStep): Seq[String] = ps.subgoals.zipWithIndex.map(updateIndex(id, filter, store))

  //def apply(p: ProofNode): String = print("", None, (_, _) => ())(p)
  def apply(p: ProofNode, id: String, limit: Int, store: (ProofNode, String) => Unit): String = print(id, Some(limit), store)(p)
  def apply(p: ProofNode, id: String, filter: (ProofStepInfo => Boolean), store: ((ProofNode, String) => Unit)): String = print(id, filter, store)(p)

}
