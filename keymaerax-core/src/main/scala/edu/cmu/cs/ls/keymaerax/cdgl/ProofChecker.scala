package edu.cmu.cs.ls.keymaerax.cdgl

import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper.{atomicOdes, sortAtomicOdes}
import edu.cmu.cs.ls.keymaerax.btactics.{Integrator, ToolProvider}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.cdgl.Proof._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr, SubstitutionHelper}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.tools.ext.QETacticTool

case class ProofException(msg: String) extends Exception {
  override def toString:String = msg
}

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

  type Indices = Map[Either[String,String],Option[Int]]
  private def collectVars(init:Indices, e:Expression):Indices = {
    var acc:Indices = init
    val etf =
      new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
          e match {
            case BaseVariable(x, ind, kind) =>
              (acc.get(Left(x)), ind) match {
                case (None, _) => acc = acc.+((Left(x), ind))
                case (Some(Some(i)), Some(j)) => acc = acc.+((Left(x), Some(Math.max(i,j))))
                case (Some(_), _) => acc = acc.+((Left(x), ind))
              }
            case DifferentialSymbol(BaseVariable(x, ind, kind)) =>
              (acc.get(Right(x)), ind) match {
                case (None, _) => acc = acc.+((Right(x), ind))
                case (Some(Some(i)), Some(j)) => acc = acc.+((Right(x), Some(Math.max(i,j))))
                case (Some(_), _) => acc = acc.+((Right(x), ind))
              }
            case _ => ()
          }
          Left(None)
        }
      }
    e match {
      case e: Program => ExpressionTraversal.traverse(etf, e)
      case e: Term => ExpressionTraversal.traverse(etf, e)
      case e: Formula => ExpressionTraversal.traverse(etf, e)
      case _ => throw ProofException("Unexpected expression in ghostVars")
    }
    acc
  }
  private def collectVars(es:List[Expression]):Indices = {
    es.foldLeft[Indices](Map())(collectVars)
  }

  private def freshIn(x:Variable, map:Indices):Boolean = {
    x match {
      case BaseVariable(name,ind,sort) =>
        (map.get(Left(name)),ind) match {
          case (None,_) => true
          case (Some(None),Some(_)) => true
          case (Some(Some(i)), Some(j)) => i < j
          case _ => false
        }
      case DifferentialSymbol(BaseVariable(name,ind,sort)) =>
        (map.get(Right(name)),ind) match {
          case (None,_) => true
          case (Some(None),Some(_)) => true
          case (Some(Some(i)), Some(j)) => i < j
          case _ => false
        }

    }
  }

  private def freshOf(x:Variable, map:Indices):Variable = {
    x match {
      case BaseVariable(name,ind,sort) =>
        map.get(Left(name)) match {
          case None => x
          case Some(None) => BaseVariable(name,Some(0),sort)
          case Some(Some(i)) => BaseVariable(name,Some(i+1),sort)
        }
      case DifferentialSymbol(BaseVariable(name,ind,sort)) =>
        map.get(Right(name)) match {
          case None => x
          case Some(None) => DifferentialSymbol(BaseVariable(name,Some(0),sort))
          case Some(Some(i)) => DifferentialSymbol(BaseVariable(name,Some(i+1),sort))
        }
    }
  }

  def ghostVar(explicit:Option[Variable], base:Variable, taboos:List[Expression]): Variable = {
    val map:Indices = collectVars(taboos)
    explicit match {
      case Some(x) =>
        if (freshIn(x,map)) {
          x
        } else {
          throw ProofException(s"Proof term specified ghost variable $x which was not fresh in $taboos")
        }
      case None => freshOf(base,map)
    }
  }

  def ghostVars(explicit:Option[List[Variable]], base:List[Variable], freshIn:List[Expression]): List[Variable] = {
    val xys:List[(Option[Variable],Variable)] = explicit match {
      case None => base.map((None,_))
      case Some(xs) => xs.zip(base).map({case(x,y) => (Some(x),y)})
    }
    xys.map({case (x,y) => ghostVar(x,y,freshIn)})
  }

  //TODO: implement
  //TODO: what do if t'=1 already
  def solve(tvar:Variable, xys:List[(Variable,Variable)], ode: ODESystem, sol:Option[List[Term]]):List[Term] = {
    sol match {
      case Some(x) => x
      case None =>
        val vars = StaticSemantics(ode).bv.toSet.++(Set(tvar)).toList.filter(_.isInstanceOf[Variable]).toList
        val initialConditions = vars.map(x => (x,x)).toMap
        val solutions = Integrator(initialConditions, tvar, ode)
        solutions.map({case Equal(_,f) =>
          xys.foldLeft(f)({case (acc, (x,y)) => URename(x,y)(acc)})})
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
        val y = ghostVar(yOpt, x, f :: G.asList)
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
        val y = ghostVar(yOpt, x, f :: G.asList)
        val f1 = URename(x,y)(f)
        val G1 = G.rename(x,y).extend(Equal(x,f1))
        val P = apply(G1, child)
        Diamond(AssignAny(x), P)
      case DRandomE(left, right, yOpt) =>
        apply(G,left) match {
          case Diamond(AssignAny(x),q) =>
            val y = ghostVar(yOpt, x, q :: G.asList)
            val G1 = G.rename(x,y).extend(q)
            val p = apply(G1, right)
            if (!StaticSemantics(p).fv.intersect(Set(x,y)).isEmpty) {
              throw ProofException(s"Postcondition $p cannot mention $x or $y in rule <:*>E")
            } else p
          case p => throw ProofException(s"Rule <:*>E not applicable to formula $p")
        }
      case ExistsI(Assign(x,f), child: Proof, yOpt:Option[Variable]) =>
        val y = ghostVar(yOpt,x, f :: G.asList)
        val f1 = URename(x,y)(f)
        val G1 = G.rename(x,y).extend(Equal(x,f1))
        val P = apply(G1, child)
        Exists(List(x), P)
      case  ExistsE(left: Proof, right: Proof, yOpt:Option[Variable])  =>
        apply(G,left) match {
          case Exists(List(x),q) =>
            val y = ghostVar(yOpt, x, q :: G.asList)
            val G1 = G.rename(x,y).extend(q)
            val p = apply(G1, right)
            if (!StaticSemantics(p).fv.intersect(Set(x,y)).isEmpty) {
              throw ProofException(s"Postcondition $p cannot mention $x or $y in rule <:*>E")
            } else p
          case p => throw ProofException(s"Rule <:*>E not applicable to subgoal $p")
        }
      case DComposeI(child) =>
        apply(G,child) match {
          case Diamond(a,Diamond(b,p)) => Diamond(Compose(a,b),p)
          case p => throw ProofException(s"Rule <;>I not applicable to subgoal $p")
        }
      case DComposeE(child) =>
        apply(G,child) match {
          case Diamond(Compose(a,b),p) => Diamond(a,Diamond(b,p))
          case p => throw ProofException(s"Rule <;>E not applicable to subgoal $p")
        }
      case DChoiceIL(child,b) =>
        apply(G,child) match {
          case Diamond(a,p) => Diamond(Choice(a,b),p)
          case p => throw ProofException(s"Rule <++>IL not applicable to subgoal $p")
        }

      case DChoiceIR(child,a) =>
        apply(G,child) match {
          case Diamond(b,p) => Diamond(Choice(a,b),p)
          case p => throw ProofException(s"Rule <++>IR not applicable to subgoal $p")
        }
      case DChoiceE(child, left, right) =>
        apply(G,child) match {
          case Diamond(Choice(a,b),p) =>
            val pp = apply(G.extend(Diamond(a,p)),left)
            val qq = apply(G.extend(Diamond(b,p)),right)
            if(pp != qq) {
              throw ProofException(s"Postconditions $pp and $qq do not match in <++>E")
            }
            pp
          case p => throw ProofException(s"Rule <++>E not applicable to subgoal $p")
        }
      case DStop(child,a) =>
        val p = apply(G,child)
        Diamond(Loop(a),p)
      case DGo(child) =>
        apply(G,child) match {
          case Diamond(a,Diamond(Loop(b),p)) =>
            if(a != b)
              throw ProofException(s"Programs $a and $b do not match in <*>G")
            Diamond(Loop(a),p)
          case p => throw ProofException(s"Rule <*>G not applicable to subgoal $p")
        }
      case DRepeatI(metric, metz, mx, init, step, post) =>
        //val met0 = BaseVariable(mx.name, Some(mx.index.map(i => i+ 1).getOrElse(0)))
        val variant = apply(G,init)
        apply(Context(List(And(Equal(mx,metric), Greater(metric,metz)), variant)), step) match {
          case Diamond(a,p2) =>
            val p3 = apply(Context(List(Equal(metric,metz),variant)),post)
            val expectedPost = And(variant, Greater(metz, metric))
            if(p2 != expectedPost)
              throw ProofException(s"Rule <*>I expected inductive step postcondition $expectedPost, got $p2")
            Diamond(Loop(a), p3)
          case p => throw ProofException(s"Rule <*>I not applicable to subgoal $p")
        }
      case DRepeatE(child, post, step) =>
        apply(G,child) match {
          case Diamond(Loop(a),p) =>
            val p1 = apply(Context(List(p)),post)
            val p2 = apply(Context(List(Diamond(a,p1))),step)
            if(p1 != p2)
              throw ProofException(s"Rule <*>E postconditions $p1 and $p2 did not match")
            p1
          case p => throw ProofException(s"Rule <*>E not applicable to subgoal $p")
        }
      case DDualI(child) =>
        apply(G,child) match {
          case Box(a,p) => Diamond(Dual(a),p)
          case p => throw ProofException(s"Rule <d>I not applicable to subgoal $p")
        }
      case DDualE(child) =>
        apply(G,child) match {
          case Diamond(Dual(a),p) => Box(a,p)
          case p => throw ProofException(s"Rule <d>E not applicable to subgoal $p")
        }
      case DSolve(ode, post, child, dc, ys, sol, dur, s, t) =>
        ???
      case DV(f, g, d, const, dur, rate, post) =>
        ???

      case BTestI(fml, child) =>
        val p1 = apply(G.extend(fml),child)
        Box(Test(fml),p1)
      case BTestE(left, right) =>
        apply(G,left) match {
          case Box(Test(p1),q) =>
            val p2 = apply(G,right)
            if(p1 != p2)
              throw ProofException(s"Assumption $p2 does not match expected $p1 in [?]E")
            q
          case p => throw ProofException(s"Rule [?]E not applicable to subogal $p")
        }
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
      case BRepeatI(pre, step, post, a1, ysOpt) =>
        val j1 = apply(G,pre)
        val xs = StaticSemantics(a1).bv.toSet.toList
        val ys = ghostVars(ysOpt, xs, a1 :: G.asList)
        val G1 = G.renames(xs,ys).extend(j1)
        apply(G1, step) match {
          case Box(a2,j2) =>
            if(a1 != a2) {
              throw ProofException(s"Programs $a1 and $a2 in [*]I must be the same")
            } else if(j1 != j2) {
              throw ProofException(s"Invariants $j1 and $j2 in [*]I must be the same")
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
      case BSolve(ode, post, child, s, t, solsOpt, ysOpt) =>
        val xs = StaticSemantics(ode).bv.toSet.toList.filter({case _ : BaseVariable => true case _ => false}: (Variable => Boolean))
        val ys = ghostVars(ysOpt, xs, List(ode))
        // TODO: assert solution
        // TODO: assert freshness
        val xys = xs.zip(ys)
        val sol = solve(t, xys, ode, solsOpt)
        val sols = xs.zip(sol)
        val g = xys.foldLeft(G)({case (acc, (x,y)) => acc.rename(x,y)})
        val con = ((t,s)::sols).foldLeft[Formula](ode.constraint)({case (acc,(x,f)) => SubstitutionHelper.replaceFree(acc)(x,f)})
        val dcFml = Forall(List(s),Imply(And(LessEqual(Number(0),s),LessEqual(s,t)),con))
        val p = apply(g.extend(GreaterEqual(t,Number(0))).extend(dcFml), child)
        val sub = sols.foldLeft[Formula](post)({case (acc,(x,f)) => SubstitutionHelper.replaceFree(acc)(x,f)})
        if(sub != p) {
            throw ProofException(s"['] with postcondition $post expected subgoal postcondition $sub, got $p")
        }
        Box(ode, post)
      case DW(ode, child, ysOpt) =>
        val xs = StaticSemantics(ode).bv.toSet.toList.filter({case _ : BaseVariable => true case _ => false}: (Variable => Boolean))
        val ys = ghostVars(ysOpt, xs, List(ode))
        val p1 = apply(G.renames(xs,ys).extend(ode.constraint),child)
        Box(ode,p1)
      case DC(left, right) =>
        val Box(ODESystem(ode,con),p) = apply(G,left)
        val Box(ODESystem(ode1,And(con1,p1)),q) = apply(G,right)
        assert(ode == ode1 && con1 == con && p1 == p)
        Box(ODESystem(ode,con),q)
      case DI(ode1, pre, step, ysOpt) =>
        val p = apply(G,pre)
        val xs = StaticSemantics(ode1).bv.toSet.toList.filter({case _ : BaseVariable => true case _ => false}: (Variable => Boolean))
        val ys = ghostVars(ysOpt, xs, ode1 :: G.asList)
        val G1 = G.renames(xs,ys).extend(ode1.constraint)
        apply(G1,step) match {
          case Box(ode2,dp) =>
            val df = deriveFormula(p)
            if (ode1 != ode2) {
              throw ProofException(s"ODEs $ode1 and $ode2 in DI should be equal")
            } else if (dp != df) {
              throw ProofException(s"Subgoal in DI should be derivative $df, was $dp")
            }
            ???
          case p => throw ProofException(s"Rule DI not applicable to formula $p")
        }
      case DG(Assign(y, y0), Plus(Times(a,yy), b), child) =>
        if (y != yy) {
          throw ProofException(s"Variables $y and $yy should be equal in DG")
        }
        apply(G,child) match {
          case Box(Compose(Assign(xy,e),ODESystem(DifferentialProduct(AtomicODE(xp,xe),c),con)),pp) =>
            if (y != xy) {
              throw ProofException(s"Expected $y and $xy equal in DG subgoal")
            } else if (xp != DifferentialSymbol(xy)) {
              throw ProofException(s"Expected $xp and ${DifferentialSymbol(xy)} equal in DG subgoal")
            } else if (e != y0) {
              throw ProofException(s"Expected $e and $y0 equal in DG subgoal")
            } else if (xe == Plus(Times(a,xy),b)) {
              throw ProofException(s"Expected $xe and ${Plus(Times(a,xy),b)} equal in DG subgoal")
            } else if (StaticSemantics(pp).fv.++(StaticSemantics(a).++(StaticSemantics(b)
                .++(StaticSemantics(con).fv.++(StaticSemantics(y0).++(G.freevars)))))
              .toSet.intersect(Set(y,DifferentialSymbol(y))).nonEmpty) {
              throw ProofException(s"Variable $y needs to be fresh in DG")
            } else Box(ODESystem(c,con),pp)
        }
      case DG(e,_,_) => throw ProofException(s"Expected ghost term $e to have shape (f*y)+g in DG")
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
          case p => throw ProofException(s"Rule |E not applicable to subgoal $p")
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
      case Mon(left,right,ysOpt) =>
        val p = apply(G,left)
        p match {
          case Box(a,p) =>
            val xs = StaticSemantics(a).bv.toSet.toList
            val ys = ghostVars(ysOpt, xs, a :: G.asList)
            val G1 = G.renames(xs,ys).extend(p)
            val q = apply(G1, right)
            Box(a,q)
          case Diamond(a,p) =>
            val xs = StaticSemantics(a).bv.toSet.toList
            val ys = ghostVars(ysOpt, xs, a :: G.asList)
            val G1 = G.renames(xs,ys).extend(p)
            val q = apply(G1, right)
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
