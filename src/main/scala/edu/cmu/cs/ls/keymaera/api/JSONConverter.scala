package edu.cmu.cs.ls.keymaera.api

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import scala.Left
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import scala.collection.immutable.Seq
import edu.cmu.cs.ls.keymaera.core.Sequent
import scala.Some
import edu.cmu.cs.ls.keymaera.core.PosInExpr

/**
 * Created by jdq on 6/13/14.
 */
object JSONConverter {

  def printPos(p: PosInExpr): Any =
    p.pos.mkString(",")

  def printNamedSymbol(n: NamedSymbol): String = "\"" + n.name + (n.index match { case Some(j) => "_" + j case _ => "" }) + "\""

  def printForm(formula: Formula): String = {
    var jsonResult: String = ""
    val fn = new ExpressionTraversalFunction {

      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        jsonResult += (e match {
          case True() => "{ \"id\": \"" + printPos(p) + "\", \"name\": \"true\"}"
          case False() => "{ \"id\": \"" + printPos(p) + "\", \"name\": \"false\"}"
          case x@PredicateConstant(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\": " + printNamedSymbol(x.asInstanceOf[PredicateConstant]) + "}"
          case ApplyPredicate(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"apply\", \"children\": [ " + printNamedSymbol(a) + ", "
          case Equals(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"equals\"" + ", \"children\": [ "
          case NotEquals(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"notEquals\"" + ", \"children\": [ "
          case ProgramEquals(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"programEquals\"" + ", \"children\": [ "
          case ProgramNotEquals(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"programNotEquals\"" + ", \"children\": [ "
          case LessThan(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"lt\"" + ", \"children\": [ "
          case LessEqual(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"leq\"" + ", \"children\": [ "
          case GreaterEqual(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"geq\"" + ", \"children\": [ "
          case GreaterThan(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"gt\"" + ", \"children\": [ "
          case Not(a) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"not\"" + ", \"children\": [ "
          case And(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"and\"" + ", \"children\": [ "
          case Or(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"or\"" + ", \"children\": [ "
          case Imply(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"imply\"" + ", \"children\": [ "
          case Equiv(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"equiv\"" + ", \"children\": [ "
          case Modality(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"modality\"" + ", \"children\": [ "
          case Forall(v, a) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"forall\", \"variables\": [" + v.map(printNamedSymbol).mkString(",") + "], \"children\": [ "
          case Exists(v, a) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"exists\", \"variables\": [" + v.map(printNamedSymbol).mkString(",") + "], \"children\": [ "
          case _ => throw new UnsupportedOperationException("not implemented yet for " + KeYmaeraPrettyPrinter.stringify(e) + " type " + e.getClass)
        })
        Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        jsonResult += (e match {
          case Number(s, i) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"" + i + "\"}"
          case x@Variable(_, _, _) => "{ \"id\": \"" + printPos(p) + "\", \"name\":" + printNamedSymbol(x.asInstanceOf[Variable]) + "}"
          case Apply(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"apply\", \"children\": [ " + printNamedSymbol(a) + ", "
          case Neg(_, a) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"neg\"" + ", \"children\": [ "
          case Derivative(_, a) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"derivative\"" + ", \"children\": [ "
          case Add(_, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"add\"" + ", \"children\": [ "
          case Subtract(_, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"subtract\"" + ", \"children\": [ "
          case Multiply(_, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"multiply\"" + ", \"children\": [ "
          case Divide(_, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"divide\"" + ", \"children\": [ "
          case Exp(_, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"Exp\"" + ", \"children\": [ "
          case _ => throw new UnsupportedOperationException("not implemented yet for " + KeYmaeraPrettyPrinter.stringify(e) + " type " + e.getClass)
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
    }
    ExpressionTraversal.traverse(fn, formula)
    jsonResult
  }

  def print(l: Seq[Formula]): String = (for(f <- l) yield KeYmaeraPrettyPrinter.stringify(f).replaceAll("\\\\", "\\\\\\\\")).mkString(",")
  def print(s: Sequent): String = print(s.ante) + " ==> " + print(s.succ)
  def print(id: String, limit: Option[Int])(p: ProofNode): String = "{ \"sequent\":\"" + (if(p.children.isEmpty) "??? " else "") + p.info.branchLabel + ": " + print(p.sequent) + "\", \"children\": [ " +
    (limit match {
      case Some(l) if l > 0 => p.children.map((ps: ProofStep) => print(id, limit.map(i => i - 1), ps)).mkString(",")
      case _ => ""}) + "]}"
  def print(id: String, limit: Option[Int], ps: ProofStep): String = "{\"rule\":\"" + ps.rule.toString + "\", \"children\": [" + subgoals(id, limit)(ps).mkString(",") + "]" + "}"

  private def updateIndex(id: String, limit: Option[Int])(in: (ProofNode, Int)): String = print(id + "/" + in._2, limit)(in._1)
  private def subgoals(id: String, limit: Option[Int])(ps: ProofStep): Seq[String] = ps.subgoals.zipWithIndex.map(updateIndex(id, limit))

  def apply(p: ProofNode): String = print("", None)(p)
  def apply(p: ProofNode, id: String, limit: Int): String = print(id, Some(limit))(p)

}
