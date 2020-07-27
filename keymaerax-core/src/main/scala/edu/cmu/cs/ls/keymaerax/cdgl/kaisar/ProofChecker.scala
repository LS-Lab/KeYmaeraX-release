package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

//import edu.cmu.cs.ls.keymaerax.cdgl.Context
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.infrastruct.UnificationMatch
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

object ProofChecker {
  val SSA: Boolean = false
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
      case DefaultSelector(f) =>
        val fv = StaticSemantics(f).fv
        fv.toSet.toList.flatMap((v: Variable) => Context.get(con, v).toList)
      case ForwardSelector(pt) => List(apply(con, pt))
      case PatternSelector(e) => Context.unify(con, e).toList.map(_._2)
    }
  }

  def methodAssumptions(con: Context, m: Method): (List[Formula], Method) = {
    m match {
      case Using(sels, m) =>
        val assms = sels.flatMap(methodAssumptions(con, _))
        val (assm, meth) = methodAssumptions(con, m)
        (assms ++ assm, meth)
      case RCF() | Auto() | Prop() | _: ByProof => (List(), m)
    }
  }

  def qeAssert(f: => Boolean, assms: List[Formula], fml: Formula, m: Method): Unit = {
    if(!f) throw new ProofCheckException(s"Couldn't prove goal ${assms.mkString(",")} |- $fml with method $m")
  }

  def rcf(assms: Set[Formula], f: Formula): Boolean = {
    edu.cmu.cs.ls.keymaerax.cdgl.ProofChecker.qeValid(Imply(assms.foldLeft[Formula](True)(And), f))
  }

  def auto(assms: Set[Formula], f: Formula): Boolean = {
    prop(assms, f, rcf)
  }

  val hyp: (Set[Formula], Formula) => Boolean = ((fs, f) => fs.contains(f))

  def contextAlphas(fmls: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    fmls.find{case _: And => true case _: Equiv => true  case False => true case _ => false} match {
      case Some(False) => true
      case Some(And(l, r)) => prop(fmls.-(And(l,r)).+(l).+(r), f, leaf)
      case Some(Equiv(l, r)) => prop(fmls.-(And(l,r)).+(l).+(r), f, leaf)
      case _ => conclusionBeta(fmls, f, leaf)
    }
  }
  def conclusionBeta(assms: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    f match {
      case And(l, r) => prop(assms, l, leaf) && prop(assms, r, leaf)
      case Equiv(l, r) => prop(assms.+(l), r) && prop(assms.+(r), l)
      case _ => contextBetas(assms, f, leaf)
    }
  }

  def contextBetas(assms: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    assms.find { case _: Or => true case _: Imply => true case _ => false } match {
      case Some(Or(l, r)) => prop(assms.-(Or(l,r)).+(l), f, leaf) || prop(assms.-(Or(l,r)).+(r), f, leaf)
      case Some(Imply(l, r)) => prop(assms.-(Imply(l,r)), l) && prop(assms.-(Imply(l,r)).+(r), f)
      case _ => leaf(assms, f)
    }
  }
  def prop(assms: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    // Alpha introduction rules
    f match {
      case True => true
      // True, False, And, Or, Imply, Equiv, Not, Box, Diamond, Forall, Cmp
      case Imply(l, r) => prop(assms.+(l), r, leaf)
      case Not(f) => prop(assms.+(f), False)
      case _ => contextAlphas(assms, f, leaf)
    }
  }

  def apply(con: Context, f: Formula, m: Method): Unit = {
    val defaultMeth = Using(List(DefaultSelector(f)), m)
    val (assms, meth) = methodAssumptions(con, defaultMeth)
    meth match {
      case  RCF() => qeAssert(rcf(assms.toSet, f), assms, f, m)
      // general-purpose auto heuristic
      case Auto() => qeAssert(auto(assms.toSet, f), assms, f, m)
      // propositional steps
      case Prop() => qeAssert(prop(assms.toSet, f), assms, f, m)
      // discharge goal with structured proof
      case ByProof(proof: Proof) => apply(con, proof)
    }
  }

  // @TODO: Extremely incomplete
  def exhaustive(es: List[Expression]): Boolean = {
    val exprs = es.sortWith((l,r) => (l, r) match {
      case (_: Greater, _: Less) => true case (_: GreaterEqual, _: Less) => true
      case (_: Greater, _: LessEqual) => true case (_: GreaterEqual, _: LessEqual) => true
      case _ => l.toString < r.toString
    })
    exprs match {
      case (Greater(l1, r1) :: Less(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (GreaterEqual(l1, r1) :: Less(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (Greater(l1, r1) :: LessEqual(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (GreaterEqual(l1, r1) :: LessEqual(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (Greater(l1, r1: Number) :: Less(l2, r2: Number) :: Nil) => l1 == l2 && r1.value < r2.value
      case (GreaterEqual(l1, r1: Number) :: Less(l2, r2: Number) :: Nil) => l1 == l2 && r1.value < r2.value
      case (Greater(l1, r1: Number) :: LessEqual(l2, r2: Number) :: Nil) => l1 == l2 && r1.value < r2.value
      case (GreaterEqual(l1, r1: Number) :: LessEqual(l2, r2: Number) :: Nil) => l1 == l2 && r1.value < r2.value
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

  def apply(con: Context, ds: DiffStatement, dc: DomainStatement): (ProveODE, Formula) = {
    ???
  }

  private def asBox(f: Formula): Box = {
    f match {
      case b: Box => b
      case _ => Box(Dual(Test(f)), True)
    }
  }
  private def asDiamond(f: Formula): Diamond = {
    f match {
      case b: Diamond => b
      case _ => Diamond(Test(f), True)
    }
  }

  private def unifyFml(p: Formula, q: Formula): Option[Formula] = {
    if (p == q) Some(p) else None
  }
  private def unifyFmls(ps: Seq[Formula]): Option[Formula] = {
    ps match {
      case Nil => None
      case p :: Nil => Some(p)
      case p :: ps => unifyFmls(ps) match {
        case None => None
        case Some(q) => unifyFml(p, q)
      }
    }
  }

  private def concatBox(p: Formula, q: Formula): Formula = {
    (p, q) match {
      case (True, _) => q
      case (_, True) => p
      case (Box(a, True), Box(b, q1)) => Box(Compose(a, b), q1)
      case (Box(a, True), q) => Box(Compose(a, Dual(Test(q))), True)
      case (Box(a, p1), Box(b, q1)) => Box(Compose(a, Compose(Dual(Test(p1)), b)), q1)
      case (p, Box(b, q1)) => Box(Compose(Dual(Test(p)), b), q1)
      case (Box(a, p1), q) => Box(Compose(a,Compose(Dual(Test(p1)), Dual(Test(q)))), True)
    }
  }

  private def unzip3[T1,T2,T3](seq:List[(T1,T2,T3)]):(List[T1],List[T2],List[T3]) = {
    seq match {
      case Nil => (Nil, Nil, Nil)
      case (x, y, z):: xyzs =>
        val (xs, ys, zs) = unzip3(xyzs)
        (xs.+:(x), ys.+:(y), zs.+:(z))
    }
  }

  private def zip3[T1,T2,T3](xs:List[T1],ys:List[T2],zs:List[T3]):List[(T1,T2,T3)] = {
    (xs, ys, zs) match {
      case (Nil, Nil, Nil) => Nil
      case (x :: xs, y :: ys, z :: zs) => (x, y, z) :: zip3(xs, ys, zs)
      case _ => throw new Exception("Mismatched lengths in zip3")
    }
  }


  def apply(con: Context, p: Proof): (Context, Formula) = {
    apply(con, Block(p.ss))
  }
  // Result is (c1, f) where c1 is the elaboration of s (but not con) into a context and f is the conclusion proved
  // by that elaborated program
  def apply(con: Context, s: Statement): (Context, Formula) = {
    s match {
      case Assert(_ , f, m) =>
        apply(con, f, m)
        (s, Box(Dual(Test(f)), True))
      case Note(x , pt,  conclusion) =>
        val res = apply(con, pt)
        if (conclusion.isDefined && conclusion.get != res) {
          throw ProofCheckException(s"Note $x expected conclusion ${conclusion.get}, got $res")
        }
        (Note(x, pt, Some(res)), res)
      case Block(ss) =>
        val (c, fs) =
          ss.foldLeft[(Context, List[Formula])](Context.empty, List()){case ((acc, accF), s) =>
            val (cc, ff) = apply(Context.+:(con, acc), s)
            (Context.+:(acc, s), accF.:+(ff))
          }
        val ff = fs.reduceRight(concatBox)
        (c, ff)
      case BoxChoice(left: Statement, right: Statement) =>
        val ((sl, fl), (sr, fr)) = (apply(con, left), apply(con, right))
        val (Box(a, p1), Box(b, p2)) = (asBox(fl), asBox(fr))
        val p = unifyFml(p1, p2).getOrElse(throw new ProofCheckException("Could not unify branches of choice"))
        val ss = BoxChoice(sl, sr)
        (ss, Box(Choice(a,b), p))
      case Switch(sel, branches: List[(Expression, Expression, Statement)]) =>
        // @TODO: proper expression patterns not just formulas
        // @TODO: Formula names
        val (patterns, conds, bodies) = unzip3(branches)
        if (!exhaustive(conds)) {
          throw ProofCheckException("Inexhaustive match in switch statement")
        }
        val (cons, fmls) = branches.map(cb => {
          val (c, f) = apply(Context.add(con, cb._1.asInstanceOf[Variable], cb._2.asInstanceOf[Formula]), cb._3)
          (c, concatBox(Box(Test(cb._2.asInstanceOf[Formula]), True), f))}
          ).unzip
        val (as, ps) = fmls.map(asBox).map{case Box(a,p) => (Dual(a),p)}.unzip
        val p = unifyFmls(ps).getOrElse(throw ProofCheckException("Switch branches failed to unify"))
        (Switch(sel, zip3(patterns, conds,cons)), Box(Dual(as.reduceRight(Choice)), p))
      case While(x , j, s) =>
        val kc = Context.+:(con, Assume(x, j))
        val (sa, fa) = apply(kc, s)
        val ss = While(x, j, sa)
        val Diamond(a, p) = asDiamond(fa)
        val fml = Diamond(Loop(a), p)
        (ss, fml)
      case BoxLoop(s: Statement) =>
        Context.lastFact(con) match {
          case None => throw ProofCheckException(s"No invariant found in $con")
          case Some(kFml) =>
            val (ss, f) = apply(con, s)
            val Box(a,p) = asBox(f)
            val res = BoxLoop(ss)
            val ff = Box(Loop(a), p)
            Context.lastFact(res) match {
              case None => throw ProofCheckException(s"Inductive step does not prove invariant")
              case Some(kFml2) if kFml != kFml2 => throw ProofCheckException(s"Inductive step $kFml2 and invariant $kFml differ")
              case Some(kFml2) => (res, ff)
            }
        }
      case ProveODE(ds: DiffStatement, dc: DomainStatement) => apply(con, ds, dc)
      // @TODO: LetFun and Match should be checked in earlier passes?
      case lf: LetFun => admitLetFun(con, lf); (lf, True)
      case Match(pat, e) =>
        try {
          UnificationMatch(pat, e);
          (Match(pat, e), True)
        } catch {
          case e: ProverException => throw ProofCheckException(s"Pattern match $pat = $e fails to unify")
        }
      case Ghost(s) =>
        // @TODO: Check scope on f
        val (ss, f) = apply(con, s)
        (Ghost(ss), True)
      case InverseGhost(s: Statement) =>
        val (ss, f) = apply(con, s)
        (InverseGhost(ss), True)
      case PrintGoal(msg) => println(s"[DEBUG] $msg: \n$con\n"); (Context.+:(con, s), True)
      case Was(now, was) =>
        val (ss, f) = apply(con, now)
        (Was(ss, was), f)
      // Proofs that succeed unconditionally
      case Modify(VarPat(x, _), rhs) =>
        if (SSA) {
          val n = x.name
          val xIdx = x.index.getOrElse(-1)
          val freshVar = Context.fresh(con, n)
          val yIdx = freshVar.index.getOrElse(-1)
          if ((yIdx > xIdx)) {
            throw ProofCheckException(s"Assignment to $x was not in static-single-assignment form")
          }
        }
        rhs match {
          case Left(f) =>
            if (SSA && StaticSemantics(f).contains(x)) {
              throw ProofCheckException(s"Assignment to $x was not admissible")
            }
            (s, Box(Assign(x,f), True))
          case Right(_) => (s, Box(AssignAny(x), True))
        }
      case Assume(pat, f) => (s, Box(Test(f), True))
      case _: Triv | _: Label => (s, True)
    }
  }
}
