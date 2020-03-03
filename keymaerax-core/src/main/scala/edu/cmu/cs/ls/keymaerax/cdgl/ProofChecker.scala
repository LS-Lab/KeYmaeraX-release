package edu.cmu.cs.ls.keymaerax.cdgl

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.cdgl.Proof._
import edu.cmu.cs.ls.keymaerax.infrastruct.SubstitutionHelper
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.tools.ext.QETacticTool

case class ProofException(msg: String) extends Exception {}

object ProofChecker {
  private def deriveFormula(p:Formula): Formula = {
    ???
  }

  private def isConjunctive(p:Formula): Boolean = {
    p match {
      case True | _ : Less | _ : LessEqual | _ : Equal | _ : NotEqual | _ : Greater | _ : GreaterEqual => true
      case And(p,q) => isConjunctive(p) && isConjunctive(q)
      case Forall(xs, f) => isConjunctive(f)
      case _ => false
    }
  }

  private def qeValid(p:Formula): Boolean = {
    val t:QETacticTool = ToolProvider.provider.qeTool().get
    val (pre, post) = p match {
      case Imply(p, q) => (p, q)
      case p => (True, p)
    }
    val fact = t.qe(Imply(pre, post)).fact
    val conclusion = fact.conclusion
    val isFormula = conclusion.ante.isEmpty && conclusion.succ.length == 1
    fact.conclusion.succ.headOption match {
      case Some(Equiv(_,True)) => isFormula && isConjunctive(pre) && isConjunctive(post) && fact.isProved
      case _ => false
    }
  }

  //TODO
  def ghostVar(explicit:Option[Variable], base:Variable, freshIn:List[Expression]): Variable = {
    explicit match {
      case Some(x) => x
      case None => base
    }
  }

  //TODO
  def ghostVars(explicit:Option[List[Variable]], base:List[Variable], freshIn:List[Expression]): List[Variable] = {
    explicit match {
      case Some(x) => x
      case None => base
    }
  }
  //TODO
  def solve(ode: ODESystem, sol:Option[List[Term]]):List[Term] = {
    sol match {
      case Some(x) => x
      case None => List()
    }
  }

  def apply(G: Context, M: Proof): Formula = {
    val Context(con) = G
    M match {
      case Triv() => True
      case DTestI(left, right) =>
        val P = apply(G, left)
        val Q = apply(G, right)
        Diamond(Test(P),Q)
      case DTestEL(child) =>
        apply(G,child) match {
          case Diamond(Test(p),_) => p
          case p => throw ProofException(s"[?]EL not applicable to formula ${p}")
        }
      case DTestER(child) =>
        apply(G,child) match {
          case Diamond(Test(_),q) => q
          case p => throw ProofException(s"[?]ER not applicable to formula ${p}")
        }
      case DAssignI(asgn@Assign(x,f), child, yOpt) =>
        val y = ghostVar(yOpt, x, List(f))
        val ren = URename(x,y)
        val g = ren(f)
        val d = G.rename(x,y).extend(Equal(x,g))
        val P = apply(d, child)
        val vars = (G.freevars ++ StaticSemantics(P).fv ++ StaticSemantics(asgn).fv).toSet
        if (vars.contains(y)) {
          throw ProofException(s"Ghost variable ${y} not fresh")
        }
        Diamond(Assign(x,f), P)
      case DAssignE(child) =>
        apply(G, child) match {
          case Diamond(Assign(x,f),pp) => SubstitutionHelper.replaceFree(pp)(x, f)
          case p => throw ProofException(s"[:=]E not applicable to formula $p")
        }

      case DRandomI(Assign(x,f), child, yOpt) =>
        val y = ghostVar(yOpt, x, List(f))
        val ren = URename(x,y)
        val g = ren(f)
        val d = G.rename(x,y).extend(Equal(x,g))
        val P = apply(d, child)
        Diamond(AssignAny(x), P)
      case DRandomE(left, right, yOpt) =>
        //TODO: Assert y fresh and doesnt escape scope
        val Exists(List(x),q) = apply(G,left)
        val y = ghostVar(yOpt, x, List())
        val P = apply(G.rename(x,y).extend(q),right)
        P
      case ExistsI(Assign(x,f), child: Proof, yOpt:Option[Variable]) =>
        val y = ghostVar(yOpt,x,List(f))
        val ren = URename(x,y)
        val g = ren(f)
        val d = G.rename(x,y).extend(Equal(x,g))
        val P = apply(d, child)
        Exists(List(x), P)
      case  ExistsE(left: Proof, right: Proof, yOpt:Option[Variable])  =>
        //TODO: Assert y fresh and doesnt escape scope
        val Diamond(AssignAny(x),q) = apply(G,left)
        val y = ghostVar(yOpt, x, List())
        val P = apply(G.rename(x,y).extend(q),right)
        P
      case DComposeI(child) =>
        val Diamond(a,Diamond(b,p)) = apply(G,child)
        Diamond(Compose(a,b),p)
      case DComposeE(child) =>
        val Diamond(Compose(a,b),p) = apply(G,child)
        Diamond(a,Diamond(b,p))
      case DChoiceIL(child,b) =>
        val Diamond(a,p) = apply(G,child)
        Diamond(Choice(a,b),p)
      case DChoiceIR(child,a) =>
        val Diamond(b,p) = apply(G,child)
        Diamond(Choice(a,b),p)
      case DChoiceE(child, left, right) =>
        val Diamond(Choice(a,b),p) = apply(G,child)
        val pp = apply(G.extend(Diamond(a,p)),left)
        val qq = apply(G.extend(Diamond(b,p)),right)
        require(pp == qq)
        pp
      case DStop(child,a) =>
        val p = apply(G,child)
        Diamond(Loop(a),p)
      case DGo(child) =>
        val Diamond(a,Diamond(Loop(b),p)) = apply(G,child)
        assert(a == b)
        Diamond(Loop(a),p)
      case DRepeatI(metric, metz, mx, init, step, post) =>
        //val met0 = BaseVariable(mx.name, Some(mx.index.map(i => i+ 1).getOrElse(0)))
        val variant = apply(G,init)
        val Diamond(a,p2) = apply(Context(List(And(Equal(mx,metric), Greater(metric,metz)), variant)), step)
        val p3 = apply(Context(List(Equal(metric,metz),variant)),post)
        assert(p2 == And(variant, Greater(metz, metric)))
        Diamond(Loop(a), p3)
      case DRepeatE(child, post, step) =>
        val Diamond(Loop(a),p) = apply(G,child)
        val p1 = apply(Context(List(p)),post)
        val p2 = apply(Context(List(Diamond(a,p1))),step)
        assert(p2 == p1)
        p1
      case DDualI(child) =>
        val Box(a,p) = apply(G,child)
        Diamond(Dual(a),p)
      case DDualE(child) =>
        val Diamond(Dual(a),p) = apply(G,child)
        Box(a,p)
      case DSolve(ode, ys, sol, dur, s, t, dc, post) =>
        ???
      case DV(f, g, d, const, dur, rate, post) =>
        ???

      case BTestI(fml, child) =>
        val p1 = apply(G.extend(fml),child)
        Box(Test(fml),p1)
      case BTestE(left, right) =>
        val Box(Test(p),q) = apply(G,left)
        val p2 = apply(G,right)
        assert(p == p2)
        q
      case BAssignI(asgn@Assign(x,f), child, yOpt) =>
        val y = ghostVar(yOpt,x,List(f))
        val ren = URename(x,y)
        val g = ren(f)
        val d = G.rename(x,y).extend(Equal(x,g))
        val P = apply(d, child)
        val vars = (G.freevars ++ StaticSemantics(P).fv ++ StaticSemantics(asgn).fv).toSet
        if (vars.contains(y)) {
          throw ProofException(s"Ghost variable ${y} not fresh")
        }
        Box(Assign(x,f), P)
      case BAssignE(child) =>
        apply(G, child) match {
          case Box(Assign(x,f),pp) =>
            SubstitutionHelper.replaceFree(pp)(x,f)
          case p => throw ProofException(s"Rule [:=]E does not apply to formula $p")
        }
      case BRandomI(x, child, yOpt) =>
        val y = ghostVar(yOpt,x,List())
        val pp = apply(G.rename(x,y), child)
        Box(AssignAny(x),pp)
      case BRandomE(child, f) =>
        apply(G,child) match {
          case Box(AssignAny(x),pp) => SubstitutionHelper.replaceFree(pp)(x,f)
          case p => throw ProofException(s"Rule [:*]E does not apply to formula $p")
        }
      case ForallI(x, child, yOpt) =>
        val y = ghostVar(yOpt, x, List())
        val pp = apply(G.rename(x,y), child)
        Forall(List(x),pp)
      case ForallE(child: Proof, f:Term) =>
        apply(G,child) match {
          case Forall(List(x),pp) => SubstitutionHelper.replaceFree(pp)(x,f)
          case p => throw ProofException(s"Rule forallE does not apply to formula $p")
        }
      case BComposeI(child) =>
        apply(G,child) match {
          case Box(a,Box(b,p)) => Box(Compose(a,b),p)
          case p => throw ProofException(s"Rule [;]I does not apply to formula $p")
        }
      case BComposeE(child) =>
        apply(G,child) match {
          case Box(Compose(a,b),p) => Box(a,Box(b,p))
          case p => throw ProofException(s"Rule [;]E does not apply to formula $p")
        }
      case BChoiceI(left, right) =>
        apply(G,left) match {
          case Box(a,p) =>
            apply(G,right) match {
              case Box(b,q) =>
                if (p != q) throw ProofException(s"Conjunct postconditions $p and $q differ in [++]I")
                else Box(Choice(a,b),p)
              case r =>throw ProofException(s"Rule [++]I not applicable with right conjunct $r")
            }
          case l => throw ProofException(s"Rule [++]I not applicable with left conjunct $l")
        }
      case BChoiceEL(child) =>
        apply(G,child) match {
          case Box(Choice(a,_),p) => Box(a,p)
          case p => throw ProofException(s"Rule [++]EL not applicable to formula $p")
        }
      case BChoiceER(child) =>
        apply(G,child) match {
          case Box(Choice(_,b),p) => Box(b,p)
          case p => throw ProofException(s"Rule [++]ER not applicable to formula $p")
        }
      // TODO: Better consistency in rename across rules
      case BRepeatI(pre, step, post) =>
        val j1 = apply(G,pre)
        apply(Context(List(j1)), step) match {
          case Box(a,j2) =>
            if(j1 != j2) {
              throw ProofException(s"Inconsistent invariants $j1 and $j2 in [*]I")
            } else {
              apply(Context(List(j1)), post)
            }
          case p => throw ProofException(s"Rule [*]I not applicable to formula $p")
        }
      case BRepeatEL(child) =>
        apply(G, child) match {
          case Box(Loop(_),p) => p
          case p => throw ProofException(s"Rule [*]EL not applicable to formula $p")
        }
      case BRepeatER(child) =>
        apply(G,child) match {
          case Box(Loop(a),p) => Box(a,Box(Loop(a),p))
          case p => throw ProofException(s"Rule [*]ER not applicable to formula $p")
        }
      case BDualI(child) =>
        apply(G,child) match {
          case Diamond(a,p) => Box(Dual(a),p)
          case p => throw ProofException(s"Rule [d]I not applicable to formula $p")
        }
      case BDualE(child) =>
        apply(G,child) match {
          case Box(Dual(a), p) => Diamond(a, p)
          case p => throw ProofException(s"Rule [d]E not applicable to formula $p")
        }
      case BSolve(ode, post, s, t, solsOpt, ysOpt) =>
        val xs = StaticSemantics(ode).bv.toSet.toList.filter({case _ : BaseVariable => true case _ => false}: (Variable => Boolean))
        val sol = solve(ode, solsOpt)
        val ys = ghostVars(ysOpt, xs, List(ode))
        // TODO: assert solution
        // TODO: assert freshness
        val xys = xs.zip(ys)
        val sols = xs.zip(sol)
        val asgn = sols.map({case (x,e) => Assign(x,e)}).fold[Program](Test(True))(Compose)
        val tasgn = Compose(Assign(t,s), asgn)
        val g = xys.foldLeft(G)({case (acc, (x,y)) => acc.rename(x,y)})
        val dcFml = Forall(List(s),Imply(And(LessEqual(Number(0),s),LessEqual(s,t)),Diamond(asgn,ode.constraint)))
        apply(g.extend(And(GreaterEqual(t,Number(0)),dcFml)), post) match {
          case Diamond(asgns, p1) =>
            if (asgn != tasgn)
              throw ProofException(s"Assignments $asgn and $tasgn mismatch in [']")
            else
              Box(ode, p1)
          case p => throw ProofException(s"Rule ['] not applicable to subgoal $p")
        }
      case DW(ode, child, ysOpt) =>
        //TODO: rename
        val xs = StaticSemantics(ode).bv.toSet.toList.filter({case _ : BaseVariable => true case _ => false}: (Variable => Boolean))
        val ys = ghostVars(ysOpt, xs, List(ode))
        val p1 = apply(G.extend(ode.constraint),child)
        Box(ode,p1)
      case DC(left, right) =>
        val Box(ODESystem(ode,con),p) = apply(G,left)
        val Box(ODESystem(ode1,And(con1,p1)),q) = apply(G,right)
        assert(ode == ode1 && con1 == con && p1 == p)
        Box(ODESystem(ode,con),q)
      case DI(pre, step) =>
        val p = apply(G,pre)
        // TODO: Context
        apply(G,step) match {
          case Box(ode,dp) =>
            val df = deriveFormula(p)
            if (dp != df) {
              throw ProofException(s"Subgoal in DI should be derivative $df, was $dp")
            }
            ???
          case p => throw ProofException(s"Rule DI not applicable to formula $p")
        }
      case DG(Assign(y, y0), Plus(Times(a,yy), b), child) =>
        //@TODO: freshness
        assert(yy == y)
        val Box(Compose(Assign(xy,e),ODESystem(DifferentialProduct(AtomicODE(xp,xe),c),con)),pp) = apply(G,child)
        assert(y == xy && xp == DifferentialSymbol(xy) && e == y0 && xe == Plus(Times(a,xy),b))
        Box(ODESystem(c,con),pp)
      case _ : DG => ???
      case AndI(left, right) =>
        val p = apply(G,left)
        val q = apply(G,right)
        And(p,q)
      case AndEL(child) =>
        apply(G,child) match {
          case And(p,_) => p
          case p => throw ProofException(s"Rule ^EL not applicable to subgoal $p")
        }
      case AndER(child) =>
        apply(G,child) match {
          case And(_,q) => q
          case p => throw ProofException(s"Rule ^ER not applicable to subgoal $p")
        }
      case OrIL(other, child) =>
        val p = apply(G,child)
        Or(p,other)
      case OrIR(other,child) =>
        val q = apply(G,child)
        Or(other,q)
      case OrE(child, left, right) =>
        apply(G,child) match {
          case Or(p,q) =>
            val r1 = apply(G.extend(p),left)
            val r2 = apply(G.extend(q),right)
            if(r1 != r2)
              throw ProofException(s"Postconditions $r1 and $r2 do not match in rule |E")
            else
              r1
          case p => throw ProofException("Rule |E not applicable to subgoal $p")
        }
      case ImplyI(fml, child) =>
        val q = apply(G.extend(fml),child)
        Imply(fml,q)
      case ImplyE(left, right) =>
        apply(G,left) match {
          case Imply(p1,q) =>
            val p2 = apply(G,right)
            if(p1 != p2)
              throw ProofException(s"Assumption $p1 and $p2 mismatch in ->E")
            else
              q
          case p => throw ProofException(s"Rule ->E not applicable to formula $p")
        }
      case EquivI(Equiv(p,q), left, right) =>
        val q1 = apply(G.extend(p),left)
        val p1 = apply(G.extend(q),right)
        if (p1 != p) {
          throw ProofException(s"Left formula $p1 does not match $p in <->I")
        } else if (q1 != q) {
          throw ProofException(s"Right formula $q1 does not match $q in <->I")
        } else
          Equiv(p,q)
      case EquivEL(child, assump) =>
        apply(G,child) match {
          case Equiv(p,q) =>
            val pp = apply(G,assump)
            if(p != pp) {
              throw ProofException(s"Assumption $pp does not match expected $p in <->EL")
            } else {
              q
            }
          case p => throw ProofException(s"Rule <->EL not applicable to subgoal $p")
        }
      case EquivER(child, assump) =>
        apply(G,child) match {
          case Equiv(p,q) =>
            val qq = apply(G,assump)
            if (q != qq) {
              throw ProofException(s"Assumption $qq does not match expected $q in <->EL")
            } else {
              p
            }
          case p => throw ProofException(s"Rule <->ER not applicable to subgoal $p")
        }
      case NotI(p, child) =>
        apply(G.extend(p),child) match {
          case False => Not(p)
          case p => throw ProofException(s"Rule !I not applicable to subgoal $p")
        }
      case NotE(left, right) =>
        apply(G,left) match {
          case Not(p) =>
            val pp = apply(G,right)
            if (p != pp) {
              throw ProofException(s"Rule !E needed $p to contradict ${Not(p)}, got $pp")
            }
            False
          case p => throw ProofException(s"Rule !E not applicable to subgoal $p")
        }
      case FalseE(child, fml) =>
        apply(G,child) match {
          case False => fml
          case p => throw ProofException(s"Rule falseE not applicable to subgoal $p")
        }
      case Hyp(p) =>
        if(G.contains(p)) G(p)
        else throw ProofException(s"Proof variable $p undefined in rule hyp with context $G")
      case Mon(left,right) =>
        val p = apply(G,left)
        // @TODO: Better context extending
        p match {
          case Box(a,p) =>
            val q = apply(Context(List(p)), right)
            Box(a,q)
          case Diamond(a,p) =>
            val q = apply(Context(List(p : Formula)), right)
            Diamond(a,q)
          case _ =>
            throw ProofException(s"Montonicity not applicable to non-modal formula ${p}")
        }
      case QE(q, child) =>
        val p = apply(G,child)
        if(!Imply(p,q).isFOL) {
          throw ProofException(s"QE formula ${p}->${q} was not FOL")
        }
        if(qeValid(Imply(p,q)))
          q
        else
          throw ProofException(s"QE formula ${Imply(p,q)} not valid")
    }
  }
}
