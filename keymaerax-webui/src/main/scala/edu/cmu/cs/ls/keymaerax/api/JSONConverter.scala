/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.api

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal
import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import spray.json._
import scala.collection.immutable.Seq
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.bellerophon.{Position, PosInExpr}

import scala.collection.mutable

// TODO fetch sequents only on demand
object JSONConverter {
  val prettyPrinter = KeYmaeraXPrettyPrinter.pp //todo use appropriate symbol table.

  def convertPos(formulaId:String, p: PosInExpr) = JsString(formulaId + ","+ p .pos.mkString(","))

  def convertNamedSymbol(n: NamedSymbol) = JsString(n.name + (n.index match { case Some(j) => "_" + j case _ => "" }))

  def convertFormula(formula: Formula, formulaId: String, nodeId: String): JsObject = {
    val jsonStack = new mutable.Stack[List[JsValue]]

    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        e match {
          case True => /* nothing to do */
          case False => /* nothing to do */
          case _ => jsonStack.push(List())
        }
        Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        e match {
          case Number(_) => /* Nothing to do here */
          case Variable(_, _, _) => /* Nothing to do here */
          case Nothing => /* Nothing to do here */
          case Anything => /* Nothing to do here */
          case _ => jsonStack.push(List())
        }
        Left(None)
      }

      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
        e match {
          case ProgramConst(_) => /* Nothing to do */
          case DifferentialProgramConst(_, _) => /* Nothing to do */
          case _ => jsonStack.push(List())
        }
        Left(None)
      }

      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        val cf = ("id" -> convertPos(formulaId, p)) :: Nil
        val o = e match {
          case True => JsObject(("name" -> JsString("true")) +: cf)
          case False => JsObject(("name" -> JsString("false")) +: cf)
          case PredOf(a, b) => JsObject(("name" -> JsString("apply")) :: ("fnName" -> convertNamedSymbol(a)) :: ("sort" -> JsString(a.sort.toString)) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Equal(a, b) => JsObject(("name" -> JsString("equals")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case NotEqual(a, b) => JsObject(("name" -> JsString("notEquals")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Less(a, b) => JsObject(("name" -> JsString("lt")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case LessEqual(a, b) => JsObject(("name" -> JsString("leq")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case GreaterEqual(a, b) => JsObject(("name" -> JsString("geq")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Greater(a, b) => JsObject(("name" -> JsString("gt")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Not(a) => JsObject(("name" -> JsString("not")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case And(a, b) => JsObject(("name" -> JsString("and")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Or(a, b) => JsObject(("name" -> JsString("or")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Imply(a, b) => JsObject(("name" -> JsString("imply")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Equiv(a, b) => JsObject(("name" -> JsString("equiv")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Box(a, b) => JsObject(("name" -> JsString("boxmodality")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Diamond(a, b) => JsObject(("name" -> JsString("diamondmodality")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Forall(v, a) => JsObject(("name" -> JsString("forall")) :: ("variables" -> JsArray(v.map(convertNamedSymbol).toList)) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Exists(v, a) => JsObject(("name" -> JsString("exists")) :: ("variables" -> JsArray(v.map(convertNamedSymbol).toList)) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case DifferentialFormula(a) => JsObject(("name" -> JsString("formuladerivative")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
        }
        jsonStack.push(jsonStack.pop() :+ o)
        Left(None)
      }

      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        val cf = ("id" -> convertPos(formulaId, p)) :: Nil
        val o = e match {
          case Number(i) => JsObject(("name" -> JsString(i.toString())) +: cf)
          case x@Variable(_, _, _) => JsObject(("name" -> convertNamedSymbol(x.asInstanceOf[Variable])) +: cf)
          case Nothing => JsObject(("name" -> JsString("Nothing")) +: cf)
          case Anything => JsObject(("name" -> JsString("Anything")) +: cf)
          case FuncOf(a, b) => JsObject(("name" -> JsString("apply")) :: ("fnName" -> convertNamedSymbol(a)) :: ("sort" -> JsString(a.sort.toString)) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Differential(a) => JsObject(("name" -> JsString("derivative")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case DifferentialSymbol(a) => JsObject(("name" -> JsString("differentialsymbol")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Neg(a) => JsObject(("name" -> JsString("neg")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Plus(a, b) => JsObject(("name" -> JsString("add")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Minus(a, b) => JsObject(("name" -> JsString("subtract")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Times(a, b) => JsObject(("name" -> JsString("multiply")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Divide(a, b) => JsObject(("name" -> JsString("divide")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Power(a, b) => JsObject(("name" -> JsString("exp")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Pair(a, b) => JsObject(("name" -> JsString("pair")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
        }
        jsonStack.push(jsonStack.pop() :+ o)
        Left(None)
      }

      override def postP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
        val cf = ("id" -> convertPos(formulaId, p)) :: Nil
        val o = e match {
          case x@ProgramConst(_) => JsObject(("name" -> convertNamedSymbol(x.asInstanceOf[ProgramConst])) +: cf)
          case x@DifferentialProgramConst(_, _) => JsObject(("name" -> convertNamedSymbol(x.asInstanceOf[DifferentialProgramConst])) +: cf)
          case Assign(_, _) => JsObject(("name" -> JsString("Assign")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case AssignAny(_) => JsObject(("name" -> JsString("NDetAssign")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case DiffAssign(_, _) => JsObject(("name" -> JsString("Assign")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Compose(_, _) => JsObject(("name" -> JsString("Sequence")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Choice(_, _) => JsObject(("name" -> JsString("Choice")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Test(_) => JsObject(("name" -> JsString("Test")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Loop(_) => JsObject(("name" -> JsString("Loop")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case AtomicODE(_, _) => JsObject(("name" -> JsString("AtomicODE")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case DifferentialProduct(_, _) => JsObject(("name" -> JsString("ODEProduct")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case ODESystem(_, _) => JsObject(("name" -> JsString("NFODEProduct")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
        }
        jsonStack.push(jsonStack.pop() :+ o)
        Left(None)
      }
    }
    jsonStack.push(List())
    ExpressionTraversal.traverse(fn, formula)
    jsonStack.pop().head.asJsObject()
  }

  def convertPosition(pos : Position) = JsObject(
    "kind" -> JsString(if (pos.isAnte) "ante" else "succ"),
    "index" -> JsNumber(pos.index0),
    "inExpr" -> convertPos("", pos.inExpr)
  )

  def convertRule(rule : Rule): JsObject = {
    val cf = ("name" -> JsString(rule.name)) :: Nil
    rule match {
      case r : AssumptionRule => JsObject(("kind" -> JsString("AssumptionRule")) :: ("pos" -> convertPosition(r.pos))
        :: ("assumption" -> convertPosition(r.assume)) :: Nil ++: cf)
      case r : PositionRule => JsObject(("kind" -> JsString("PositionRule"))
        :: ("pos" -> convertPosition(r.pos)) :: Nil ++: cf)
      case r : TwoPositionRule => JsObject(("kind" -> JsString("TwoPositionRule"))
        :: ("pos1" -> convertPosition(r.pos1)) :: ("pos2" -> convertPosition(r.pos2)) :: Nil ++: cf)
      case _ => JsObject(("kind" -> JsString("UnspecificRule")) +: cf)
    }
  }

  def convertSubderivation(provable: Provable): JsObject = {
    JsObject("kind" -> JsString("Subderivation"), "name" -> JsString("unknown"))
  }

  def convert(l: Seq[Formula], ante: String, nodeId: String): JsArray =
    JsArray(l.zipWithIndex.map(f => JsObject(
        "nodeId"  -> JsString(nodeId),
        "id"      -> JsString(ante + ":" + f._2),
        "formula" -> convertFormula(f._1, ante + ":" + f._2, nodeId)
      )).toList)
  def convert(s: Sequent, nodeId: String): JsObject =
    JsObject(
      "nodeId"  -> JsString(nodeId),
      "ante"    -> convert(s.ante, "ante", nodeId),
      "succ"    -> convert(s.succ, "succ", nodeId)
    )

}
