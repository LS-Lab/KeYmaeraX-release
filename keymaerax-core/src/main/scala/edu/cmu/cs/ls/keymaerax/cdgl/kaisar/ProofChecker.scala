package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

//import edu.cmu.cs.ls.keymaerax.cdgl.Context
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.infrastruct.UnificationMatch
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

object ProofChecker {
  // @TODO: Implement builtin forward proof rules
  val nullaryBuiltin: Map[String, Formula] = Map()
  val unaryBuiltin: Map[String, Expression => Formula] = Map()
  val binaryBuiltin: Map[String, (Expression, Expression) => Formula] = Map()

  def ptToExpression(con: Context, pt: ProofTerm): Expression = {
    pt match {
      case ProofInstance(e) => e
      case _ => apply(con, pt)
    }
  }

  def apply(con: Context, pt: ProofTerm): Formula = {
    pt match {
      case ProofVar(s) if nullaryBuiltin.contains(s.name) => nullaryBuiltin(s.name)
      case ProofApp(ProofVar(s), pt1) if unaryBuiltin.contains(s.name) => unaryBuiltin(s.name)(ptToExpression(con, pt1))
      case ProofApp(ProofApp(ProofVar(s), pt1), pt2) if binaryBuiltin.contains(s.name) =>
        binaryBuiltin(s.name)(ptToExpression(con, pt1), ptToExpression(con, pt2))
      case ProofVar(s) =>
        Context.get(con, s) match {
          case Some(fml) => fml
          case None => throw ProofCheckException(s"Undefined proof variable $s")
        }
      case ProofApp(pt, ProofInstance(e)) =>
        apply(con, pt) match {
          case Forall(List(x), p) => USubst(SubstitutionPair(x, e) :: Nil)(p)
          case _ => throw ProofCheckException("Tried to instantiate non-quantifier")
        }
      case ProofApp(pt1, pt2) =>
        (apply(con, pt1), apply(con, pt2)) match {
          case (Imply(p, q), r)  if p == r => throw ProofCheckException(s"Argument $r in proof term does not match expected $p")
          case (Imply(p, q), r)  => q
          case _ => throw ProofCheckException("Tried modus ponens on non-implication")
        }
      case _ => throw ProofCheckException(s"Ill-typed forward proof term $pt")
    }
  }

  def methodAssumptions(con: Context, m: Selector): List[Formula] = {
    m match {
      case ForwardSelector(pt) => List(apply(con, pt))
      case PatternSelector(e) => Context.unify(con, e).toList.map(_._2)
    }
  }

  def methodAssumptions(con: Context, m: Method): List[Formula] = {
    m match {
      case Using(sels, m) =>
        val assms = sels.flatMap(methodAssumptions(con, _))
        val assm = methodAssumptions(con, m)
        assms ++ assm
      case RCF() | Auto() | Prop() | _: ByProof => List()
    }
  }

  def apply(con: Context, f: Formula, m: Method): Unit = {
    // @TODO: Implement prop and auto

  }

  // @TODO: Extremely incomplete
  def exhaustive(es: List[Expression]): Boolean = {
    es match {
      case (Greater(l1, r1) :: Less(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (GreaterEqual(l1, r1) :: Less(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (Greater(l1, r1) :: LessEqual(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (GreaterEqual(l1, r1) :: LessEqual(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case _ => false
    }
  }

  def admitLetFun(con: Context, lf: LetFun): Unit = {
    val LetFun(f, args, body) = lf
    val sigBody = StaticSemantics.signature(body)
    val sig = Context.signature(con)
    val unboundFunctions = sigBody.--(KaisarProof.builtin ++ sig)
    if (sig.contains(lf.asFunction)) {
      throw ProofCheckException(s"Multiply-defined function definition ${f.name}")
    } else if (unboundFunctions.nonEmpty) {
      throw ProofCheckException(s"Definition of function ${f.name} refers to undefined symbols: $unboundFunctions")
    }
  }

  def apply(con: Context, ds: DiffStatement, dc: DomainStatement): ProveODE = {
    ???
  }

  // Result is elaborated s but not con
  def apply(con: Context, s: Statement): Context = {
    s match {
      case Assert(_ , f, m) =>
        apply(con, f, m)
        s
      case Note(x , pt,  conclusion) =>
        val res = apply(con, pt)
        if (conclusion.isDefined && conclusion.get != res) {
          throw ProofCheckException(s"Note $x expected conclusion ${conclusion.get}, got $res")
        }
        s
      case Block(ss) =>
        ss.foldLeft[Context](Context.empty){case (acc, s) =>
          apply(Context.+:(con, acc), s)
          Context.+:(acc, s)
        }
      case BoxChoice(left: Statement, right: Statement) =>
        BoxChoice(apply(con, left), apply(con, right))
      case Switch(pats: List[(Expression, Statement)]) =>
        // @TODO: proper expression patterns not just formulas
        // @TODO: Formula names
        val (conds, bodies) = pats.unzip
        if (!exhaustive(conds)) {
          throw ProofCheckException("Inexhaustive match in switch statement")
        }
        val cons = pats.map(cb => apply(Context.add(con, ???, cb._1.asInstanceOf[Formula]), cb._2))
        Switch(conds.zip(cons))
      case While(x , j, s) =>
        val kc = Context.+:(con, Assume(x, j))
        While(x, j, apply(kc, s))
      case BoxLoop(s: Statement) =>
        Context.lastFact(con) match {
          case None => throw ProofCheckException(s"No invariant found in $con")
          case Some(kFml) =>
            val res = BoxLoop(apply(con, s))
            Context.lastFact(res) match {
              case None => throw ProofCheckException(s"Inductive step does not prove invariant")
              case Some(kFml2) if kFml != kFml2 => throw ProofCheckException(s"Inductive step $kFml2 and invariant $kFml differ")
              case Some(kFml2) => BoxLoop(res)
            }
        }
      case ProveODE(ds: DiffStatement, dc: DomainStatement) => apply(con, ds, dc)
      // @TODO: LetFun and Match should be checked in earlier passes?
      case lf: LetFun => admitLetFun(con, lf); lf
      case Match(pat, e) =>
        try {
          UnificationMatch(pat, e);
          Match(pat, e)
        } catch {
          case e: ProverException => throw ProofCheckException(s"Pattern match $pat = $e fails to unify")
        }
      case Ghost(s) => Ghost(apply(con, s))
      case InverseGhost(s: Statement) => InverseGhost(apply(con, s))
      case PrintGoal(msg) => println(s"[DEBUG] $msg: \n$con\n"); Context.+:(con, s)
      case Was(now, was) =>
        val res = apply(con, now)
        Was(res, was)
      // Proofs that succeed unconditionally
      case _: Modify | _: Triv | _: Label | _: Assume => s
    }
  }
}
