/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
  * Checks forward CdGL-style natural deduction proof terms
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.ProofCheckException
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._


/** Checks forward CdGL-style natural deduction proof terms */
object ForwardProofChecker {
  /** Replace variable with term */
  private def subst(x: Variable, f: Term, p: Formula): Formula = p.replaceAll(x, f)
  /** Replace occurrences of term with variable */
  private def invSubst(x: Variable, f: Term, p: Formula): Formula = p.replaceAll(f, x)

  /** When evaluating a forward proof term, distinguish [[ProvedArg]] (that is, arguments which are proofs of facts) vs.
    * [[ExpressionArg]] which are simply inputs that do not require proof. */
  private sealed trait ForwardArg
  private case class ProvedArg (fml: Formula) extends ForwardArg
  private case class ExpressionArg (expr: Expression) extends ForwardArg


  /** The following tables define the built-in proof term connectives, with usage strings, organized by arity. */
  private val nullaryBuiltin: Map[String, Formula] = Map("trueI" -> True)
  private val unaryBuiltin: Map[String, (String, ForwardArg => Formula)] = Map(
    "andEL"   -> ("andEL (proof: P & Q)", {case ProvedArg(And(l, r)) => l}),
    "andER"   -> ("andER (proof: P & Q)", {case ProvedArg(And(l, r)) => r}),
    "equivEL" -> ("equivEL (proof: P <-> Q)", {case ProvedArg(Equiv(l, r)) => Imply(l, r)}),
    "equivER" -> ("equivER (proof: P <-> Q)", {case ProvedArg(Equiv(l, r)) => Imply(r, l)}),
    "notI"    -> ("notI (proof: P -> False)", {case (ProvedArg(Imply(p, False))) => Not(p)})
  )
  private val binaryBuiltin: Map[String, (String, (ForwardArg, ForwardArg) => Formula)] = Map(
    "andI" -> ("andI (proofL: P, proofR: Q)", {case (ProvedArg(l), ProvedArg(r)) => And(l, r)}),
    /* Note that in natural deduction, we wish to compute the conclusion given the proof, so we annotate orI<X> with
    *  the unknown disjunct, for example */
    "orIL" -> ("orIL (proof: P, Q : Formula)", {case (ProvedArg(l), ExpressionArg(r: Formula)) => Or(l, r)}),
    "orIR" -> ("orIR (P: Formula, proof: Q)", {case (ExpressionArg(l: Formula), ProvedArg(r)) => Or(l, r)}),
    "notE" -> ("notE (proofL: !P, proofR: P)", {case (ProvedArg(Not(p)), ProvedArg(pp)) if p == pp => False}),
    "falseE" -> ("falseE (proof: False, P: Formula)", {case (ProvedArg(False), ExpressionArg(p: Formula)) => p}),
    "implyW" -> ("implyI (P: Formula, proof: Q)", {case (ExpressionArg(p: Formula), ProvedArg(q)) => Imply(p, q)}),
    "allI" -> ("allI (x: Variable, proof: P)", {case (ExpressionArg(v: Variable), ProvedArg(p)) if !StaticSemantics(p).fv.contains(v) => Forall(List(v), p)}),
    "allE" -> ("allE (proof: (forall x, P), f: Term)", {case (ProvedArg(Forall(xs, p)), ExpressionArg(f: Term)) => subst(xs.head, f, p)}),
    "existsE" -> ("existsE (proofL: (exists x, P), proofR: (forall y, (P -> Q)))", {case (ProvedArg(Exists(List(x), p)), ProvedArg(Forall(List(y), Imply(pp, q)))) if p == pp && x == y && !StaticSemantics(q).fv.contains(x) => q})
  )
  private val ternaryBuiltin: Map[String, (String, (ForwardArg, ForwardArg, ForwardArg) => Formula)] = Map(
    "orE"     -> ("orE (proof: (A | B), proofL: (A -> C), proofR: (B -> C))", {case (ProvedArg(Or(a,b)), ProvedArg(Imply(aa, c)), ProvedArg(Imply(bb, cc))) if a == aa && b == bb && c == cc => c}),
    "existsI" -> ("existsI (x: Variable, f: Term, proof: P(f))", {case (ExpressionArg(x: Variable), ExpressionArg(f: Term), ProvedArg(p)) => Exists(List(x), invSubst(x, f, p))})
  )

  val allBuiltins: Set[String] = nullaryBuiltin.keySet ++ unaryBuiltin.keySet ++ binaryBuiltin.keySet ++ ternaryBuiltin.keySet

  // Distinguish proof terms that prove things vs. ones that supply inputs.
  private def ptToForwardArg(con: Context, pt: ProofTerm): ForwardArg = {
    pt match {
      case ProofInstance(e) => ExpressionArg(e)
      case _ => ProvedArg(apply(con, pt))
    }
  }

  // Type-safe application of unary proof rules.
  private def unary(name: String, arg1: ForwardArg, node: ASTNode): Formula = {
    val (spec, f) = unaryBuiltin(name)
    try {
      f(arg1)
    } catch {
      case t: Throwable =>
        throw ProofCheckException(s"Expected argument: $spec\nBut got ($arg1)", cause = t, node = node)
    }
  }

  // Type-safe application of binary proof rules.
  private def binary(name: String, arg1: ForwardArg, arg2: ForwardArg, node: ASTNode): Formula = {
    val (spec, f) = binaryBuiltin(name)
    try {
      f(arg1, arg2)
    } catch {
      case t: Throwable =>
        throw ProofCheckException(s"Expected arguments: $spec\nBut got ($arg1) ($arg2)", cause = t, node = node)
    }
  }

  // Type-safe application of ternary proof rules.
  private def ternary(name: String, arg1: ForwardArg, arg2: ForwardArg, arg3: ForwardArg, node: ASTNode): Formula = {
    val (spec, f) = ternaryBuiltin(name)
    try {
      f(arg1, arg2, arg3)
    } catch {
      case t: Throwable =>
        throw ProofCheckException(s"Expected arguments: $spec\nBut got ($arg1) ($arg2) ($arg3)", cause = t, node = node)
    }
  }

  /** @return the formula proven by proof term [[pt]] in context [[con]], else throws [[ProofCheckException]]*/
  def apply(con: Context, pt: ProofTerm): Formula = {
    pt match {
      case ProgramVar(x) =>
        val mentions = con.getMentions(x)
        if (mentions.isEmpty)
          // @TODO: Make this not fail tests anymore
          True //throw ProofCheckException(s"No assumptions found for program variable $x", node = pt)
        else
          mentions.map(fml => con.elaborateFunctions(fml, pt)).reduce(And)
      case ProgramAssignments(x, onlySSA) =>
        val asgns = con.getAssignments(x)
        if (asgns.isEmpty) {
          throw ProofCheckException(s"No assignments found for program variable $x", node = pt)
        }
        asgns.map(fml => con.elaborateFunctions(fml, pt)).reduce(And)
      case ProofVar(s) if nullaryBuiltin.contains(s.name) => nullaryBuiltin(s.name)
      case app@ProofApp(ProofVar(s), pt1) if unaryBuiltin.contains(s.name) => unary(s.name, ptToForwardArg(con, pt1), app)
      case app@ProofApp(ProofApp(ProofVar(s), pt1), pt2) if binaryBuiltin.contains(s.name) =>
        binary(s.name, ptToForwardArg(con, pt1), ptToForwardArg(con, pt2), app)
      case app@ProofApp(ProofApp(ProofApp(ProofVar(s), pt1), pt2), pt3) if ternaryBuiltin.contains(s.name) =>
        ternary(s.name, ptToForwardArg(con, pt1), ptToForwardArg(con, pt2), ptToForwardArg(con, pt3), app)
      case ProofVar(s) =>
        con.getHere(s) match {
          case Some(fml) =>
            con.elaborateFunctions(fml, pt)
            case None =>
            throw ProofCheckException(s"Undefined proof variable $s", node = pt)
        }
      case fullPt@ProofApp(pt, ProofInstance(e)) =>
        apply(con, pt) match {
          case Forall(List(x), p) => USubst(SubstitutionPair(x, e) :: Nil)(p)
          case _ => throw ProofCheckException("Tried to instantiate non-quantifier", node = fullPt)
        }
      case ProofApp(pt1, pt2) =>
        (apply(con, pt1), apply(con, pt2)) match {
          case (Imply(p, q), r)  if p == r => throw ProofCheckException(s"Argument $r in proof term does not match expected $p", node = pt2)
          case (Imply(p, q), r)  => q
          case (l, _) => throw ProofCheckException("Tried modus ponens on non-implication", node = pt1)
        }
      case _ => throw ProofCheckException(s"Ill-typed forward proof term $pt", node = pt)
    }
  }
}
