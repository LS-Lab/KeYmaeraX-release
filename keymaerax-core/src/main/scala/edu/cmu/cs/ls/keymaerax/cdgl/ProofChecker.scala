package edu.cmu.cs.ls.keymaerax.cdgl

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.cdgl.Proof._
import edu.cmu.cs.ls.keymaerax.infrastruct.SubstitutionHelper

case class ProofException(msg: String) extends Exception {}

object ProofChecker {

  private def deriveFormula(p:Formula): Formula = {
    ???
  }

  private def qeValid(p:Formula): Boolean = false

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
      case DTestI(left, right) =>
        val P = apply(G, left)
        val Q = apply(G, right)
        Diamond(Test(P),Q)
      case DTestEL(child) =>
        val Diamond(Test(p),_) = apply(G,child)
        p
      case DTestER(child) =>
        val Diamond(Test(_),q) = apply(G,child)
        q
      case DAssignI(Assign(x,f), child, yOpt) =>
        val y = ghostVar(yOpt, x, List(f))
        val ren = URename(x,y)
        val g = ren(f)
        val d = G.rename(x,y).extend(Equal(x,g))
        val P = apply(d, child)
        Diamond(Assign(x,f), P)
      case DAssignE(Assign(x,f), child) =>
        // TODO: Make sound
        val Diamond(Assign(xx,ff),pp) = apply(G, child)
        assert(xx == x && ff == f)
        SubstitutionHelper.replaceFree(pp)(x,f)
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
      case BAssignI(Assign(x,f), child, yOpt) =>
        val y = ghostVar(yOpt,x,List(f))
        val ren = URename(x,y)
        val g = ren(f)
        val d = G.rename(x,y).extend(Equal(x,g))
        val P = apply(d, child)
        Box(Assign(x,f), P)
      case BAssignE(Assign(x,f), child) =>
        // TODO: Make sound
        val Box(Assign(xx,ff),pp) = apply(G, child)
        assert(xx == x && ff == f)
        SubstitutionHelper.replaceFree(pp)(x,f)
      case BRandomI(x, child, yOpt) =>
        val y = ghostVar(yOpt,x,List())
        val pp = apply(G.rename(x,y), child)
        Box(AssignAny(x),pp)
      case BRandomE(child, f) =>
        val Box(AssignAny(x),pp) = apply(G,child)
        SubstitutionHelper.replaceFree(pp)(x,f)
      case ForallI(x:Variable, child: Proof, yOpt:Variable) =>
        val y = ghostVar(yOpt, x, List())
        val pp = apply(G.rename(x,y), child)
        Forall(List(x),pp)
      case ForallE(child: Proof, f:Term) =>
        val Forall(List(x),pp) = apply(G,child)
        SubstitutionHelper.replaceFree(pp)(x,f)
      case BComposeI(child) =>
        val Box(a,Box(b,p)) = apply(G,child)
        Box(Compose(a,b),p)
      case BComposeE(child) =>
        val Box(Compose(a,b),p) = apply(G,child)
        Box(a,Box(b,p))
      case BChoiceI(left, right) =>
        val Box(a,p) = apply(G,left)
        val Box(b,q) = apply(G,right)
        assert(p == q)
        Box(Choice(a,b),p)
      case BChoiceEL(child) =>
        val Box(Choice(a,_),p) = apply(G,child)
        Box(a,p)
      case BChoiceER(child) =>
        val Box(Choice(_,b),p) = apply(G,child)
        Box(b,p)
        // TODO: Better consistency in rename across rules
      case BRepeatI(pre, step, post) =>
        val j1 = apply(G,pre)
        val Box(a,j2) = apply(Context(List(j1)), step)
        assert(j1 == j2)
        apply(Context(List(j1)), post)
      case BRepeatEL(child) =>
        val Box(Loop(_),p) = apply(G, child)
        p
      case BRepeatER(child) =>
        val Box(Loop(a),p) = apply(G,child)
        Box(a,Box(Loop(a),p))
      case BDualI(child) =>
        val Diamond(a,p) = apply(G,child)
        Box(Dual(a),p)
      case BDualE(child) =>
        val Box(Dual(a),p) = apply(G,child)
        Diamond(a,p)
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
        val Diamond(asgns,p1) = apply(g.extend(And(GreaterEqual(t,Number(0)),dcFml)), post)
        assert(asgn == tasgn)
        Box(ode,p1)
      case DW(ode, child, ysOpt) =>
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
        val Box(ode,dp) = apply(G,step)
        assert(dp == deriveFormula(p))
        ???
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
        val And(p,_) = apply(G,child)
        p
      case AndER(child) =>
        val And(_,q) = apply(G,child)
        q
      case OrIL(other, child) =>
        val p = apply(G,child)
        Or(p,other)
      case OrIR(other,child) =>
        val q = apply(G,child)
        Or(other,q)
      case OrE(child, left, right) =>
        val Or(p,q) = apply(G,child)
        val r1 = apply(G.extend(p),left)
        val r2 = apply(G.extend(q),right)
        assert(r1 == r2)
        r1
      case ImplyI(fml, child) =>
        val q = apply(G.extend(fml),child)
        Imply(fml,q)
      case ImplyE(left, right) =>
        val Imply(p1,q) = apply(G,left)
        val p2 = apply(G,right)
        assert(p1 == p2)
        q
      case EquivI(Equiv(p,q), left, right) =>
        val q1 = apply(G.extend(p),left)
        val p1 = apply(G.extend(q),right)
        assert(p1 == p && q1 == q)
        Equiv(p,q)
      case EquivEL(child, assump) =>
        val Equiv(p,q) = apply(G,child)
        val pp = apply(G,assump)
        assert(p == pp)
        q
      case EquivER(child, assump) =>
        val Equiv(p,q) = apply(G,child)
        val qq = apply(G,assump)
        assert(q == qq)
        p
      case NotI(p, child) =>
        val False = apply(G.extend(p),child)
        Not(p)
      case NotE(left, right) =>
        val Not(p) = apply(G,left)
        val pp = apply(G,right)
        assert(p == pp)
        False
      case Hyp(p) => G(p)
      case Mon(left,right) =>
        // @TODO: Better context extending
        apply(G,left) match {
          case Box(a,p) =>
            val q = apply(Context(List(p)), right)
            Box(a,q)
          case Diamond(a,p) =>
            val q = apply(Context(List(p : Formula)), right)
            Diamond(a,q)
        }
      case QE(q, child) =>
         val p = apply(G,child)
         assert(qeValid(Imply(p,q)))
         q
    }
  }
}
